module cassowary.amoeba;

import core.stdc.string : memset, memcpy;

@nogc:
nothrow:

enum AM_OK          =  0;
enum AM_FAILED      = -1;
enum AM_UNSATISFIED = -2;
enum AM_UNBOUND     = -3;

enum AM_LESSEQUAL   = 1;
enum AM_EQUAL       = 2;
enum AM_GREATEQUAL  = 3;

enum AM_REQUIRED    = cast(Float)1000000000;
enum AM_STRONG      = cast(Float)1000000;
enum AM_MEDIUM      = cast(Float)1000;
enum AM_WEAK        = cast(Float)1;

version (AM_USE_FLOAT)
{
	alias Float = float;
	enum FloatEpsilon = 1e-4f;
}
else
{
	alias Float = double;
	enum FloatEpsilon = 1e-6;
}

alias Allocf = void* function (void *ud, void *ptr, size_t nsize, size_t osize);

/// external variable, corresponds to the variable created by you the user
enum AM_EXTERNAL = 0;
/// slack symbol, used to represent inequalities
enum AM_SLACK    = 1;
/// error symbol, used to represent non-required constraints
enum AM_ERROR    = 2;
/// dummy variable, always zero, used to keep track of the impact of an external variable in the tableau
enum AM_DUMMY    = 3;

pragma(inline, true)
{
	auto isexternal(Key)(Key key)  { return key.type == AM_EXTERNAL; }
	auto isslack(Key)(Key key)     { return key.type == AM_SLACK; }
	auto iserror(Key)(Key key)     { return key.type == AM_ERROR; }
	auto isdummy(Key)(Key key)     { return key.type == AM_DUMMY; }
	auto ispivotable(Key)(Key key) { return isslack(key) || iserror(key); }
}

enum AM_POOLSIZE     = 4096;
enum AM_MIN_HASHSIZE = 4;
enum AM_MAX_SIZET    = ((~cast(size_t)0)-100);

struct Symbol
{
	import mir.bitmanip : bitfields;
	mixin(bitfields!(
		uint, "id",    30,
		uint, "type",   2,
	));
	debug string label;
}

struct MemPool
{
	size_t size;
	void*  freed;
	void*  pages;

	this(size_t size) @nogc nothrow
	{
		this.size  = size;
		assert(size > (void*).sizeof && size < AM_POOLSIZE/4);
	}
}

struct Entry
{
	int    next;
	Symbol key;
}

struct Table
{
	size_t size;
	size_t count;
	size_t entry_size;
	size_t lastfree;
	Entry  *hash;
}

struct VarEntry
{
	Entry     entry;
	Variable *variable;
}

struct ConsEntry
{
	Entry       entry;
	Constraint *constraint;
}

struct Term
{
	Entry entry;
	Float multiplier;
}

struct Row
{
	Entry  entry;
	Symbol infeasible_next;
	Table  terms;
	Float  constant;
}

struct Variable
{
	Symbol      sym;
	Symbol      dirty_next;
	uint        refcount;
	Solver     *solver;
	Constraint *constraint;
	Float       edit_value;
	Float       value;

	int id() { return sym.id; }
	void usevariable() @nogc nothrow { ++refcount; }
}

struct Constraint
{
	Row     expression;
	Symbol  marker;
	Symbol  other;
	int     relation;
	Solver *solver;
	Float   strength;
}

struct Solver
{
	Allocf  allocf;
	void      *ud;
	Row        objective;
	Table      vars;            /* symbol . VarEntry */
	Table      constraints;     /* symbol . ConsEntry */
	Table      rows;            /* symbol . Row */
	MemPool    varpool;
	MemPool    conspool;
	uint       symbol_count;
	uint       constraint_count;
	uint       auto_update;
	Symbol     infeasible_rows;
	Symbol     dirty_vars;
}

/* utils */

int approx(Float a, Float b)
{
	return a > b ? (a - b < FloatEpsilon) : (b - a < FloatEpsilon);
}

int nearZero(Float a)
{
	return approx(a, 0.0f);
}

void initSymbol(Solver *solver, Symbol *sym, int type)
{
	if (sym.id == 0)
		*sym = newSymbol(solver, type);
}

void freePool(Solver *solver, MemPool *pool) {
	const size_t offset = AM_POOLSIZE - (void*).sizeof;
	while (pool.pages !is null) {
		void *next = *cast(void**)(cast(char*)pool.pages + offset);
		solver.allocf(solver.ud, pool.pages, 0, AM_POOLSIZE);
		pool.pages = next;
	}
	*pool = MemPool(pool.size);
}

void *allocMem(Solver *solver, MemPool *pool)
{
	void *obj = pool.freed;
	if (obj is null) {
		const size_t offset = AM_POOLSIZE - (void*).sizeof;
		void* end = void;
		auto newpage = solver.allocf(solver.ud, null, AM_POOLSIZE, 0);
		*cast(void**)(cast(char*)newpage + offset) = pool.pages;
		pool.pages = newpage;
		end = cast(char*)newpage + (offset/pool.size-1)*pool.size;
		while (end != newpage) {
			*cast(void**)end = pool.freed;
			pool.freed = cast(void**)end;
			end = cast(char*)end - pool.size;
		}
		return end;
	}
	pool.freed = *cast(void**)obj;
	return obj;
}

void freeMem(MemPool *pool, void *obj)
{
	*cast(void**)obj = pool.freed;
	pool.freed = obj;
}

Symbol newSymbol(Solver *solver, int type)
{
	Symbol sym;
	uint id = ++solver.symbol_count;
	if (id > 0x3FFFFFFF) id = solver.symbol_count = 1;
	assert(type >= AM_EXTERNAL && type <= AM_DUMMY);
	sym.id   = id;
	sym.type = type;
	return sym;
}


/* hash table */

pragma(inline, true)
{
@nogc nothrow:
	// #define key(entry) (((Entry*)(entry)).key)
	auto key(E)(E entry) { return (cast(Entry*)(entry)).key; }

	// #define offset(lhs, rhs) ((int)((char*)(lhs) - (char*)(rhs)))
	auto offset(L, R)(L lhs, R rhs) { return cast(int)(cast(char*)(lhs) - cast(char*)(rhs)); }
	// #define index(h, i)      ((Entry*)((char*)(h) + (i)))
	auto index(H, I)(H h, I i) { return cast(Entry*)(cast(char*)(h) + (i)); }
}

void delKey(Table *t, Entry *entry)
{
	entry.key = Symbol(), --t.count;
}

void initTable(Table *t, size_t entry_size)
{
	memset(t, 0, (*t).sizeof), t.entry_size = entry_size;
}

Entry *mainPosition(const Table *t, Symbol key)
{
	return index(t.hash, (key.id & (t.size - 1))*t.entry_size);
}

void resetTable(Table *t)
{
	t.count = 0;
	memset(t.hash, 0, t.lastfree = t.size * t.entry_size);
}

size_t hashSize(Table *t, size_t len) {
	size_t newsize = AM_MIN_HASHSIZE;
	const size_t max_size = (AM_MAX_SIZET / 2) / t.entry_size;
	while (newsize < max_size && newsize < len)
		newsize <<= 1;
	assert((newsize & (newsize - 1)) == 0);
	return newsize < len ? 0 : newsize;
}

void freeTable(Solver *solver, Table *t)
{
	size_t size = t.size*t.entry_size;
	if (size) solver.allocf(solver.ud, t.hash, 0, size);
	initTable(t, t.entry_size);
}

size_t resizeTable(Solver *solver, Table *t, size_t len) {
	size_t i, oldsize = t.size * t.entry_size;
	Table nt = *t;
	nt.size = hashSize(t, len);
	nt.lastfree = nt.size*nt.entry_size;
	nt.hash = cast(Entry*)solver.allocf(solver.ud, null, nt.lastfree, 0);
	memset(nt.hash, 0, nt.size*nt.entry_size);
	for (i = 0; i < oldsize; i += nt.entry_size) {
		Entry *e = index(t.hash, i);
		if (e.key.id != 0) {
			Entry *ne = newKey(solver, &nt, e.key);
			if (t.entry_size > Entry.sizeof)
				memcpy(ne + 1, e + 1, t.entry_size-Entry.sizeof);
		}
	}
	if (oldsize) solver.allocf(solver.ud, t.hash, 0, oldsize);
	*t = nt;
	return t.size;
}

Entry *newKey(Solver *solver, Table *t, Symbol key)
{
	if (t.size == 0) resizeTable(solver, t, AM_MIN_HASHSIZE);
	for (;;) {
		Entry *mp = mainPosition(t, key);
		if (mp.key.id != 0) {
			Entry *f = null;
			Entry *othern = void;
			while (t.lastfree > 0) {
				Entry *e = index(t.hash, t.lastfree -= t.entry_size);
				if (e.key.id == 0 && e.next == 0)  { f = e; break; }
			}
			if (!f) { resizeTable(solver, t, t.count*2); continue; }
			assert(f.key.id == 0);
			othern = mainPosition(t, mp.key);
			if (othern != mp) {
				Entry *next;
				while ((next = index(othern, othern.next)) != mp)
					othern = next;
				othern.next = offset(f, othern);
				memcpy(f, mp, t.entry_size);
				if (mp.next) f.next += offset(mp, f), mp.next = 0;
			}
			else {
				if (mp.next != 0) f.next = offset(mp, f) + mp.next;
				else assert(f.next == 0);
				mp.next = offset(f, mp), mp = f;
			}
		}
		mp.key = key;
		return mp;
	}
}

Entry *getTable(const Table *t, Symbol key)
{
	Entry *e;
	if (t.size == 0 || key.id == 0) return null;
	e = mainPosition(t, key);
	for (; e.key.id != key.id; e = index(e, e.next))
		if (e.next == 0) return null;
	return e;
}

Entry *setTable(Solver *solver, Table *t, Symbol key) {
	Entry *e;
	assert(key.id != 0);
	if ((e = cast(Entry*)getTable(t, key)) !is null) return e;
	e = newKey(solver, t, key);
	if (t.entry_size > Entry.sizeof)
		memset(e + 1, 0, t.entry_size-Entry.sizeof);
	++t.count;
	return e;
}

int nextEntry(const(Table) *t, Entry **pentry) {
	size_t i = *pentry ? offset(*pentry, t.hash) + t.entry_size : 0;
	size_t size = t.size*t.entry_size;
	for (; i < size; i += t.entry_size) {
		Entry *e = index(t.hash, i);
		if (e.key.id != 0) { *pentry = e; return 1; }
	}
	*pentry = null;
	return 0;
}


/* expression (row) */

int isConstant(Row *row)
{
	return row.terms.count == 0;
}

void freeRow(Solver *solver, Row *row)
{
	freeTable(solver, &row.terms);
}

void resetRow(Row *row)
{
	row.constant = 0.0f;
	resetTable(&row.terms);
}

void initRow(Row *row)
{
	// key(row) = Symbol();
	(cast(Entry*)(row)).key  = Symbol();
	row.infeasible_next = Symbol();
	row.constant = 0.0f;
	initTable(&row.terms, Term.sizeof);
}

void multiply(Row *row, Float multiplier)
{
	Term *term = null;
	row.constant *= multiplier;
	while (nextEntry(&row.terms, cast(Entry**)&term))
		term.multiplier *= multiplier;
}

/// Insert a symbol into the row with a given multiplier.
///
/// If the symbol already exists in the row, the multiplier will be
/// added to the existing multiplier. If the resulting multiplier
/// is zero, the symbol will be removed from the row.
void addVar(Solver *solver, Row *row, Symbol sym, Float value)
{
	Term *term;
	if (sym.id == 0) return;
	if ((term = cast(Term*)getTable(&row.terms, sym)) is null)
		term = cast(Term*)setTable(solver, &row.terms, sym);
	if (nearZero(term.multiplier += value))
		delKey(&row.terms, &term.entry);
}

void addRow(Solver *solver, Row *row, const Row *other, Float multiplier)
{
	Term *term = null;
	row.constant += other.constant*multiplier;
	while (nextEntry(&other.terms, cast(Entry**)&term))
		addVar(solver, row, key(term), term.multiplier*multiplier);
}

void solveFor(Solver *solver, Row *row, Symbol entry, Symbol exit)
{
	Term *term = cast(Term*)getTable(&row.terms, entry);
	Float reciprocal = 1.0f / term.multiplier;
	assert(entry.id != exit.id && !nearZero(term.multiplier));
	delKey(&row.terms, &term.entry);
	multiply(row, -reciprocal);
	if (exit.id != 0) addVar(solver, row, exit, reciprocal);
}

void substitute(Solver *solver, Row *row, Symbol entry, const Row *other)
{
	Term *term = cast(Term*)getTable(&row.terms, entry);
	if (!term) return;
	delKey(&row.terms, &term.entry);
	addRow(solver, row, other, term.multiplier);
}


/* variables & constraints */

Variable *sym2var(Solver *solver, Symbol sym)
{
	VarEntry *ve = cast(VarEntry*)getTable(&solver.vars, sym);
	assert(ve !is null);
	return ve.variable;
}

Variable* newVariable(Solver *solver)
{
	Variable *var = cast(Variable*)allocMem(solver, &solver.varpool);
	Symbol sym = newSymbol(solver, AM_EXTERNAL);
	VarEntry *ve = cast(VarEntry*)setTable(solver, &solver.vars, sym);
	assert(ve.variable is null);
	memset(var, 0, (*var).sizeof);
	var.sym      = sym;
	var.refcount = 1;
	var.solver   = solver;
	ve.variable  = var;
	return var;
}

void delVariable(Variable *var)
{
	if (var && --var.refcount <= 0) {
		Solver *solver = var.solver;
		VarEntry *e = cast(VarEntry*)getTable(&solver.vars, var.sym);
		assert(e !is null);
		delKey(&solver.vars, &e.entry);
		remove(var.constraint);
		freeMem(&solver.varpool, var);
	}
}

Constraint* newConstraint(Solver *solver, Float strength)
{
	Constraint *cons = cast(Constraint*)allocMem(solver, &solver.conspool);
	memset(cons, 0, (*cons).sizeof);
	cons.solver   = solver;
	cons.strength = nearZero(strength) ? AM_REQUIRED : strength;
	initRow(&cons.expression);
	(cast(Entry*)(cons)).key.id = ++solver.constraint_count;
	(cast(Entry*)(cons)).key.type = AM_EXTERNAL;
	(cast(ConsEntry*)setTable(solver, &solver.constraints, key(cons))).constraint = cons;
	return cons;
}

void delConstraint(Constraint *cons)
{
	Solver *solver = cons ? cons.solver : null;
	Term *term = null;
	ConsEntry *ce;
	if (cons is null) return;
	remove(cons);
	ce = cast(ConsEntry*)getTable(&solver.constraints, key(cons));
	assert(ce !is null);
	delKey(&solver.constraints, &ce.entry);
	while (nextEntry(&cons.expression.terms, cast(Entry**)&term))
		delVariable(sym2var(solver, key(term)));
	freeRow(solver, &cons.expression);
	freeMem(&solver.conspool, cons);
}

Constraint *cloneConstraint(Constraint *other, Float strength)
{
	Constraint *cons;
	if (other is null) return null;
	cons = newConstraint(other.solver,
			nearZero(strength) ? other.strength : strength);
	mergeConstraint(cons, other, 1.0f);
	cons.relation = other.relation;
	return cons;
}

int mergeConstraint(Constraint *cons, Constraint *other, Float multiplier)
{
	Term *term = null;
	if (cons is null || other is null || cons.marker.id != 0
			|| cons.solver != other.solver) return AM_FAILED;
	if (cons.relation == AM_GREATEQUAL) multiplier = -multiplier;
	cons.expression.constant += other.expression.constant*multiplier;
	while (nextEntry(&other.expression.terms, cast(Entry**)&term)) {
		sym2var(cons.solver, key(term)).usevariable;
		addVar(cons.solver, &cons.expression, key(term),
				term.multiplier*multiplier);
	}
	return AM_OK;
}

void resetConstraint(Constraint *cons)
{
	Term *term = null;
	if (cons is null) return;
	remove(cons);
	cons.relation = 0;
	while (nextEntry(&cons.expression.terms, cast(Entry**)&term))
		delVariable(sym2var(cons.solver, key(term)));
	resetRow(&cons.expression);
}

int addTerm(Constraint *cons, Variable *var, Float multiplier = 1.0)
{
	if (cons is null || var is null || cons.marker.id != 0 ||
			cons.solver != var.solver) return AM_FAILED;
	assert(var.sym.id != 0);
	assert(var.solver == cons.solver);
	if (cons.relation == AM_GREATEQUAL) multiplier = -multiplier;
	addVar(cons.solver, &cons.expression, var.sym, multiplier);
	var.usevariable;
	return AM_OK;
}

int addConstant(Constraint *cons, Float constant)
{
	if (cons is null || cons.marker.id != 0) return AM_FAILED;
	if (cons.relation == AM_GREATEQUAL)
		cons.expression.constant -= constant;
	else
		cons.expression.constant += constant;
	return AM_OK;
}

int setRelation(Constraint *cons, int relation)
{
	assert(relation >= AM_LESSEQUAL && relation <= AM_GREATEQUAL);
	if (cons is null || cons.marker.id != 0 || cons.relation != 0)
		return AM_FAILED;
	if (relation != AM_GREATEQUAL) multiply(&cons.expression, -1.0f);
	cons.relation = relation;
	return AM_OK;
}


// /* Cassowary algorithm */

int hasEdit(Variable *var)
{
	return var !is null && var.constraint !is null;
}

int hasConstraint(Constraint *cons)
{
	return cons !is null && cons.marker.id != 0;
}

void autoUpdate(Solver *solver, int auto_update)
{
	solver.auto_update = auto_update;
}

void infeasible(Solver *solver, Row *row) {
	if (isdummy(row.infeasible_next)) return;
	row.infeasible_next.id = solver.infeasible_rows.id;
	row.infeasible_next.type = AM_DUMMY;
	solver.infeasible_rows = key(row);
}

void markDirty(Solver *solver, Variable *var) {
	if (var.dirty_next.type == AM_DUMMY) return;
	var.dirty_next.id = solver.dirty_vars.id;
	var.dirty_next.type = AM_DUMMY;
	solver.dirty_vars = var.sym;
}

void substituteRows(Solver *solver, Symbol var, Row *expr) {
	Row *row = null;
	while (nextEntry(&solver.rows, cast(Entry**)&row)) {
		substitute(solver, row, var, expr);
		if (isexternal(key(row)))
			markDirty(solver, sym2var(solver, key(row)));
		else if (row.constant < 0.0f)
			infeasible(solver, row);
	}
	substitute(solver, &solver.objective, var, expr);
}

int getRow(Solver *solver, Symbol sym, Row *dst) {
	Row *row = cast(Row*)getTable(&solver.rows, sym);
	(cast(Entry*)(dst)).key = Symbol();
	if (row is null) return AM_FAILED;
	delKey(&solver.rows, &row.entry);
	dst.constant   = row.constant;
	dst.terms      = row.terms;
	return AM_OK;
}

int putRow(Solver *solver, Symbol sym, /*const*/ Row *src) {
	Row *row = cast(Row*)setTable(solver, &solver.rows, sym);
	row.constant = src.constant;
	row.terms    = src.terms;
	return AM_OK;
}

void mergeRow(Solver *solver, Row *row, Symbol var, Float multiplier)
{
	Row *oldrow = cast(Row*)getTable(&solver.rows, var);
	if (oldrow) addRow(solver, row, oldrow, multiplier);
	else addVar(solver, row, var, multiplier);
}

int optimize(Solver *solver, Row *objective) {
	for (;;) {
		Symbol enter = Symbol(), exit = Symbol();
		Float r, min_ratio = Float.max;
		Row tmp = void;
		Row *row = null;
		Term *term = null;

		assert(solver.infeasible_rows.id == 0);
		while (nextEntry(&objective.terms, cast(Entry**)&term)) {
			if (!isdummy(key(term)) && term.multiplier < 0.0f)
			{ enter = key(term); break; }
		}
		if (enter.id == 0) return AM_OK;

		while (nextEntry(&solver.rows, cast(Entry**)&row)) {
			term = cast(Term*)getTable(&row.terms, enter);
			if (term is null || !ispivotable(key(row))
					|| term.multiplier > 0.0f) continue;
			r = -row.constant / term.multiplier;
			if (r < min_ratio || (approx(r, min_ratio)
						&& key(row).id < exit.id))
				min_ratio = r, exit = key(row);
		}
		assert(exit.id != 0);
		if (exit.id == 0) return AM_FAILED;

		getRow(solver, exit, &tmp);
		solveFor(solver, &tmp, enter, exit);
		substituteRows(solver, enter, &tmp);
		if (objective != &solver.objective)
			substitute(solver, objective, enter, &tmp);
		putRow(solver, enter, &tmp);
	}
}

Row makeRow(Solver *solver, Constraint *cons) {
	Term *term = null;
	Row row;
	initRow(&row);
	row.constant = cons.expression.constant;
	while (nextEntry(&cons.expression.terms, cast(Entry**)&term)) {
		markDirty(solver, sym2var(solver, key(term)));
		mergeRow(solver, &row, key(term), term.multiplier);
	}
	if (cons.relation != AM_EQUAL) {
		initSymbol(solver, &cons.marker, AM_SLACK);
		addVar(solver, &row, cons.marker, -1.0f);
		if (cons.strength < AM_REQUIRED) {
			initSymbol(solver, &cons.other, AM_ERROR);
			addVar(solver, &row, cons.other, 1.0f);
			addVar(solver, &solver.objective, cons.other, cons.strength);
		}
	}
	else if (cons.strength >= AM_REQUIRED) {
		initSymbol(solver, &cons.marker, AM_DUMMY);
		addVar(solver, &row, cons.marker, 1.0f);
	}
	else {
		initSymbol(solver, &cons.marker, AM_ERROR);
		initSymbol(solver, &cons.other,  AM_ERROR);
		addVar(solver, &row, cons.marker, -1.0f);
		addVar(solver, &row, cons.other,   1.0f);
		addVar(solver, &solver.objective, cons.marker, cons.strength);
		addVar(solver, &solver.objective, cons.other,  cons.strength);
	}
	if (row.constant < 0.0f) multiply(&row, -1.0f);
	return row;
}

void removeErrors(Solver *solver, Constraint *cons)
{
	if (iserror(cons.marker))
		mergeRow(solver, &solver.objective, cons.marker, -cons.strength);
	if (iserror(cons.other))
		mergeRow(solver, &solver.objective, cons.other, -cons.strength);
	if (isConstant(&solver.objective))
		solver.objective.constant = 0.0f;
	cons.marker = cons.other = Symbol();
}

int addWithArtificial(Solver *solver, Row *row, Constraint *cons)
{
	Symbol a = newSymbol(solver, AM_SLACK);
	Term *term = null;
	Row tmp;
	int ret;
	--solver.symbol_count; /* artificial variable will be removed */
	initRow(&tmp);
	addRow(solver, &tmp, row, 1.0f);
	putRow(solver, a, row);
	initRow(row), row = null; /* row is useless */
	optimize(solver, &tmp);
	ret = nearZero(tmp.constant) ? AM_OK : AM_UNBOUND;
	freeRow(solver, &tmp);
	if (getRow(solver, a, &tmp) == AM_OK) {
		Symbol entry = Symbol();
		if (isConstant(&tmp)) { freeRow(solver, &tmp); return ret; }
		while (nextEntry(&tmp.terms, cast(Entry**)&term))
			if (ispivotable(key(term))) { entry = key(term); break; }
		if (entry.id == 0) { freeRow(solver, &tmp); return AM_UNBOUND; }
		solveFor(solver, &tmp, entry, a);
		substituteRows(solver, entry, &tmp);
		putRow(solver, entry, &tmp);
	}
	while (nextEntry(&solver.rows, cast(Entry**)&row)) {
		term = cast(Term*)getTable(&row.terms, a);
		if (term) delKey(&row.terms, &term.entry);
	}
	term = cast(Term*)getTable(&solver.objective.terms, a);
	if (term) delKey(&solver.objective.terms, &term.entry);
	if (ret != AM_OK) remove(cons);
	return ret;
}

int tryAddRow(Solver *solver, Row *row, Constraint *cons)
{
	Symbol subject = Symbol();
	Term *term = null;
	while (nextEntry(&row.terms, cast(Entry**)&term))
		if (isexternal(key(term))) { subject = key(term); break; }
	if (subject.id == 0 && ispivotable(cons.marker)) {
		Term *mterm = cast(Term*)getTable(&row.terms, cons.marker);
		if (mterm.multiplier < 0.0f) subject = cons.marker;
	}
	if (subject.id == 0 && ispivotable(cons.other)) {
		Term *mterm = cast(Term*)getTable(&row.terms, cons.other);
		if (mterm.multiplier < 0.0f) subject = cons.other;
	}
	if (subject.id == 0) {
		while (nextEntry(&row.terms, cast(Entry**)&term))
			if (!isdummy(key(term))) break;
		if (term is null) {
			if (nearZero(row.constant))
				subject = cons.marker;
			else {
				freeRow(solver, row);
				return AM_UNSATISFIED;
			}
		}
	}
	if (subject.id == 0)
		return addWithArtificial(solver, row, cons);
	solveFor(solver, row, subject, Symbol());
	substituteRows(solver, subject, row);
	putRow(solver, subject, row);
	return AM_OK;
}

Symbol getLeavingRow(Solver *solver, Symbol marker)
{
	Symbol first = Symbol(), second = Symbol(), third = Symbol();
	Float r1 = Float.max, r2 = Float.max;
	Row *row = null;
	while (nextEntry(&solver.rows, cast(Entry**)&row)) {
		Term *term = cast(Term*)getTable(&row.terms, marker);
		if (term is null) continue;
		if (isexternal(key(row))) third = key(row);
		else if (term.multiplier < 0.0f) {
			Float r = -row.constant / term.multiplier;
			if (r < r1) r1 = r, first = key(row);
		}
		else {
			Float r = row.constant / term.multiplier;
			if (r < r2) r2 = r, second = key(row);
		}
	}
	return first.id ? first : second.id ? second : third;
}

void deltaEditConstant(Solver *solver, Float delta, Constraint *cons)
{
	Row *row;
	if ((row = cast(Row*)getTable(&solver.rows, cons.marker)) !is null)
	{ if ((row.constant -= delta) < 0.0f) infeasible(solver, row); return; }
	if ((row = cast(Row*)getTable(&solver.rows, cons.other)) !is null)
	{ if ((row.constant += delta) < 0.0f) infeasible(solver, row); return; }
	while (nextEntry(&solver.rows, cast(Entry**)&row)) {
		Term *term = cast(Term*)getTable(&row.terms, cons.marker);
		if (term is null) continue;
		row.constant += term.multiplier*delta;
		if (isexternal(key(row)))
			markDirty(solver, sym2var(solver, key(row)));
		else if (row.constant < 0.0f)
			infeasible(solver, row);
	}
}

void dualOptimize(Solver *solver)
{
	while (solver.infeasible_rows.id != 0) {
		Row tmp = void;
		Row *row =
			cast(Row*)getTable(&solver.rows, solver.infeasible_rows);
		Symbol enter = Symbol(), exit = key(row), curr;
		Term *objterm = void;
		Term *term = null;
		Float r, min_ratio = Float.max;
		solver.infeasible_rows = row.infeasible_next;
		row.infeasible_next = Symbol();
		if (row.constant >= 0.0f) continue;
		while (nextEntry(&row.terms, cast(Entry**)&term)) {
			if (isdummy(curr = key(term)) || term.multiplier <= 0.0f)
				continue;
			objterm = cast(Term*)getTable(&solver.objective.terms, curr);
			r = objterm ? objterm.multiplier / term.multiplier : 0.0f;
			if (min_ratio > r) min_ratio = r, enter = curr;
		}
		assert(enter.id != 0);
		getRow(solver, exit, &tmp);
		solveFor(solver, &tmp, enter, exit);
		substituteRows(solver, enter, &tmp);
		putRow(solver, enter, &tmp);
	}
}

void *defaultAllocFunc(void *ud, void *ptr, size_t nsize, size_t osize)
{
	import core.stdc.stdlib : free, abort, realloc;
	void *newptr;
	cast(void)ud, cast(void)osize;
	if (nsize == 0)
	{
		free(ptr);
		return null;
	}
	newptr = realloc(ptr, nsize);
	if (newptr is null)
		abort();
	return newptr;
}

Solver *newSolver(Allocf allocf, void *ud)
{
	Solver *solver;
	if (allocf is null) allocf = &defaultAllocFunc;
	if ((solver = cast(Solver*)allocf(ud, null, Solver.sizeof, 0)) is null)
		return null;
	memset(solver, 0, (*solver).sizeof);
	solver.allocf = allocf;
	solver.ud     = ud;
	initRow(&solver.objective);
	initTable(&solver.vars, VarEntry.sizeof);
	initTable(&solver.constraints, ConsEntry.sizeof);
	initTable(&solver.rows, Row.sizeof);
	solver.varpool  = MemPool(Variable.sizeof);
	solver.conspool = MemPool(Constraint.sizeof);
	return solver;
}

void delSolver(Solver *solver)
{
	ConsEntry *ce = null;
	Row *row = null;
	while (nextEntry(&solver.constraints, cast(Entry**)&ce))
		freeRow(solver, &ce.constraint.expression);
	while (nextEntry(&solver.rows, cast(Entry**)&row))
		freeRow(solver, row);
	freeRow(solver, &solver.objective);
	freeTable(solver, &solver.vars);
	freeTable(solver, &solver.constraints);
	freeTable(solver, &solver.rows);
	freePool(solver, &solver.varpool);
	freePool(solver, &solver.conspool);
	solver.allocf(solver.ud, solver, 0, (*solver).sizeof);
}

void resetSolver(Solver *solver, int clear_constraints)
{
	Entry *entry = null;
	if (!solver.auto_update) updateVars(solver);
	while (nextEntry(&solver.vars, &entry)) {
		Constraint **cons = &(cast(VarEntry*)entry).variable.constraint;
		remove(*cons);
		*cons = null;
	}
	assert(nearZero(solver.objective.constant));
	assert(solver.infeasible_rows.id == 0);
	assert(solver.dirty_vars.id == 0);
	if (!clear_constraints) return;
	resetRow(&solver.objective);
	while (nextEntry(&solver.constraints, &entry)) {
		Constraint *cons = (cast(ConsEntry*)entry).constraint;
		if (cons.marker.id == 0) continue;
		cons.marker = cons.other = Symbol();
	}
	while (nextEntry(&solver.rows, &entry)) {
		delKey(&solver.rows, entry);
		freeRow(solver, cast(Row*)entry);
	}
}

void updateVars(Solver *solver)
{
	while (solver.dirty_vars.id != 0) {
		Variable *var = sym2var(solver, solver.dirty_vars);
		Row *row = cast(Row*)getTable(&solver.rows, var.sym);
		solver.dirty_vars = var.dirty_next;
		var.dirty_next = Symbol();
		var.value = row ? row.constant : 0.0f;
	}
}

int add(Constraint *cons)
{
	Solver *solver = cons ? cons.solver : null;
	int ret, oldsym = solver ? solver.symbol_count : 0;
	Row row;
	if (solver is null || cons.marker.id != 0) return AM_FAILED;
	row = makeRow(solver, cons);
	if ((ret = tryAddRow(solver, &row, cons)) != AM_OK) {
		removeErrors(solver, cons);
		solver.symbol_count = oldsym;
	}
	else {
		optimize(solver, &solver.objective);
		if (solver.auto_update) updateVars(solver);
	}
	return ret;
}

void remove(Constraint *cons)
{
	Solver *solver;
	Symbol marker;
	Row tmp;
	if (cons is null || cons.marker.id == 0) return;
	solver = cons.solver, marker = cons.marker;
	removeErrors(solver, cons);
	if (getRow(solver, marker, &tmp) != AM_OK) {
		Symbol exit = getLeavingRow(solver, marker);
		assert(exit.id != 0);
		getRow(solver, exit, &tmp);
		solveFor(solver, &tmp, marker, exit);
		substituteRows(solver, marker, &tmp);
	}
	freeRow(solver, &tmp);
	optimize(solver, &solver.objective);
	if (solver.auto_update) updateVars(solver);
}

int setStrength(Constraint *cons, Float strength)
{
	if (cons is null) return AM_FAILED;
	strength = nearZero(strength) ? AM_REQUIRED : strength;
	if (cons.strength == strength) return AM_OK;
	if (cons.strength >= AM_REQUIRED || strength >= AM_REQUIRED)
	{ remove(cons), cons.strength = strength; return add(cons); }
	if (cons.marker.id != 0) {
		Solver *solver = cons.solver;
		Float diff = strength - cons.strength;
		mergeRow(solver, &solver.objective, cons.marker, diff);
		mergeRow(solver, &solver.objective, cons.other,  diff);
		optimize(solver, &solver.objective);
		if (solver.auto_update) updateVars(solver);
	}
	cons.strength = strength;
	return AM_OK;
}

int addEdit(Variable *var, Float strength)
{
	Solver *solver = var ? var.solver : null;
	Constraint *cons;
	if (var is null || var.constraint !is null) return AM_FAILED;
	assert(var.sym.id != 0);
	if (strength > AM_STRONG) strength = AM_STRONG;
	cons = newConstraint(solver, strength);
	setRelation(cons, AM_EQUAL);
	addTerm(cons, var, 1.0f); /* var must have positive signture */
	addConstant(cons, -var.value);
	if (add(cons) != AM_OK) assert(0);
	var.constraint = cons;
	var.edit_value = var.value;
	return AM_OK;
}

void delEdit(Variable *var)
{
	if (var is null || var.constraint is null) return;
	delConstraint(var.constraint);
	var.constraint = null;
	var.edit_value = 0.0f;
}

void suggest(Variable *var, Float value)
{
	Solver *solver = var ? var.solver : null;
	Float delta;
	if (var is null) return;
	if (var.constraint is null) {
		addEdit(var, AM_MEDIUM);
		assert(var.constraint !is null);
	}
	delta = value - var.edit_value;
	var.edit_value = value;
	deltaEditConstant(solver, delta, var.constraint);
	dualOptimize(solver);
	if (solver.auto_update) updateVars(solver);
}
