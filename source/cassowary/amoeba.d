module cassowary.amoeba;

import core.stdc.string : memset, memcpy;

extern(C):
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

alias am_Allocf = void* function (void *ud, void *ptr, size_t nsize, size_t osize);

enum AM_EXTERNAL = 0;
enum AM_SLACK    = 1;
enum AM_ERROR    = 2;
enum AM_DUMMY    = 3;

pragma(inline, true)
{
@nogc nothrow:
	auto am_isexternal(Key)(Key key)  { return key.type == AM_EXTERNAL; }
	auto am_isslack(Key)(Key key)     { return key.type == AM_SLACK; }
	auto am_iserror(Key)(Key key)     { return key.type == AM_ERROR; }
	auto am_isdummy(Key)(Key key)     { return key.type == AM_DUMMY; }
	auto am_ispivotable(Key)(Key key) { return am_isslack(key) || am_iserror(key); }
}

enum AM_POOLSIZE     = 4096;
enum AM_MIN_HASHSIZE = 4;
enum AM_MAX_SIZET    = ((~cast(size_t)0)-100);

struct Symbol
{
	import mir.bitmanip : bitfields;
	mixin(bitfields!(
		uint, "id",    30,
		uint, "type",   2,));
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
	am_Allocf  allocf;
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

int approx(Float a, Float b) @nogc nothrow
{
	return a > b ? (a - b < FloatEpsilon) : (b - a < FloatEpsilon);
}

int nearzero(Float a) @nogc nothrow
{
	return approx(a, 0.0f);
}

void initsymbol(Solver *solver, Symbol *sym, int type)
{
	if (sym.id == 0)
		*sym = am_newsymbol(solver, type);
}

void freepool(Solver *solver, MemPool *pool) {
    const size_t offset = AM_POOLSIZE - (void*).sizeof;
    while (pool.pages !is null) {
        void *next = *cast(void**)(cast(char*)pool.pages + offset);
        solver.allocf(solver.ud, pool.pages, 0, AM_POOLSIZE);
        pool.pages = next;
    }
    *pool = MemPool(pool.size);
}

void *alloc(Solver *solver, MemPool *pool) {
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

void am_free(MemPool *pool, void *obj) {
    *cast(void**)obj = pool.freed;
    pool.freed = obj;
}

Symbol am_newsymbol(Solver *solver, int type) {
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
	// #define am_key(entry) (((am_Entry*)(entry)).key)
	auto am_key(E)(E entry) { return (cast(Entry*)(entry)).key; }

	// #define am_offset(lhs, rhs) ((int)((char*)(lhs) - (char*)(rhs)))
	auto am_offset(L, R)(L lhs, R rhs) { return cast(int)(cast(char*)(lhs) - cast(char*)(rhs)); }
	// #define am_index(h, i)      ((am_Entry*)((char*)(h) + (i)))
	auto am_index(H, I)(H h, I i) { return cast(Entry*)(cast(char*)(h) + (i)); }
}

void am_delkey(Table *t, Entry *entry)
{
	entry.key = Symbol(), --t.count;
}

void am_inittable(Table *t, size_t entry_size)
{
	memset(t, 0, (*t).sizeof), t.entry_size = entry_size;
}

Entry *am_mainposition(const Table *t, Symbol key) @nogc nothrow
{
	return am_index(t.hash, (key.id & (t.size - 1))*t.entry_size);
}

void am_resettable(Table *t)
{
	t.count = 0;
	memset(t.hash, 0, t.lastfree = t.size * t.entry_size);
}

size_t am_hashsize(Table *t, size_t len) {
    size_t newsize = AM_MIN_HASHSIZE;
    const size_t max_size = (AM_MAX_SIZET / 2) / t.entry_size;
    while (newsize < max_size && newsize < len)
        newsize <<= 1;
    assert((newsize & (newsize - 1)) == 0);
    return newsize < len ? 0 : newsize;
}

void am_freetable(Solver *solver, Table *t)
{
    size_t size = t.size*t.entry_size;
    if (size) solver.allocf(solver.ud, t.hash, 0, size);
    am_inittable(t, t.entry_size);
}

size_t am_resizetable(Solver *solver, Table *t, size_t len) {
    size_t i, oldsize = t.size * t.entry_size;
    Table nt = *t;
    nt.size = am_hashsize(t, len);
    nt.lastfree = nt.size*nt.entry_size;
    nt.hash = cast(Entry*)solver.allocf(solver.ud, null, nt.lastfree, 0);
    memset(nt.hash, 0, nt.size*nt.entry_size);
    for (i = 0; i < oldsize; i += nt.entry_size) {
        Entry *e = am_index(t.hash, i);
        if (e.key.id != 0) {
            Entry *ne = am_newkey(solver, &nt, e.key);
            if (t.entry_size > Entry.sizeof)
                memcpy(ne + 1, e + 1, t.entry_size-Entry.sizeof);
        }
    }
    if (oldsize) solver.allocf(solver.ud, t.hash, 0, oldsize);
    *t = nt;
    return t.size;
}
Entry *am_newkey(Solver *solver, Table *t, Symbol key) {
    if (t.size == 0) am_resizetable(solver, t, AM_MIN_HASHSIZE);
    for (;;) {
        Entry *mp = am_mainposition(t, key);
        if (mp.key.id != 0) {
            Entry *f = null;
			Entry *othern = void;
            while (t.lastfree > 0) {
                Entry *e = am_index(t.hash, t.lastfree -= t.entry_size);
                if (e.key.id == 0 && e.next == 0)  { f = e; break; }
            }
            if (!f) { am_resizetable(solver, t, t.count*2); continue; }
            assert(f.key.id == 0);
            othern = am_mainposition(t, mp.key);
            if (othern != mp) {
                Entry *next;
                while ((next = am_index(othern, othern.next)) != mp)
                    othern = next;
                othern.next = am_offset(f, othern);
                memcpy(f, mp, t.entry_size);
                if (mp.next) f.next += am_offset(mp, f), mp.next = 0;
            }
            else {
                if (mp.next != 0) f.next = am_offset(mp, f) + mp.next;
                else assert(f.next == 0);
                mp.next = am_offset(f, mp), mp = f;
            }
        }
        mp.key = key;
        return mp;
    }
}

Entry *am_gettable(const Table *t, Symbol key) @nogc nothrow
{
    Entry *e;
    if (t.size == 0 || key.id == 0) return null;
    e = am_mainposition(t, key);
    for (; e.key.id != key.id; e = am_index(e, e.next))
        if (e.next == 0) return null;
    return e;
}

Entry *am_settable(Solver *solver, Table *t, Symbol key) {
    Entry *e;
    assert(key.id != 0);
    if ((e = cast(Entry*)am_gettable(t, key)) !is null) return e;
    e = am_newkey(solver, t, key);
    if (t.entry_size > Entry.sizeof)
        memset(e + 1, 0, t.entry_size-Entry.sizeof);
    ++t.count;
    return e;
}

int am_nextentry(const(Table) *t, Entry **pentry) {
    size_t i = *pentry ? am_offset(*pentry, t.hash) + t.entry_size : 0;
    size_t size = t.size*t.entry_size;
    for (; i < size; i += t.entry_size) {
        Entry *e = am_index(t.hash, i);
        if (e.key.id != 0) { *pentry = e; return 1; }
    }
    *pentry = null;
    return 0;
}


/* expression (row) */

int am_isconstant(Row *row)
{
	return row.terms.count == 0;
}

void am_freerow(Solver *solver, Row *row)
{
	am_freetable(solver, &row.terms);
}

void am_resetrow(Row *row)
{
	row.constant = 0.0f;
	am_resettable(&row.terms);
}

void am_initrow(Row *row) {
    // am_key(row) = Symbol();
	(cast(Entry*)(row)).key  = Symbol();
    row.infeasible_next = Symbol();
    row.constant = 0.0f;
    am_inittable(&row.terms, Term.sizeof);
}

void am_multiply(Row *row, Float multiplier) {
    Term *term = null;
    row.constant *= multiplier;
    while (am_nextentry(&row.terms, cast(Entry**)&term))
        term.multiplier *= multiplier;
}

void am_addvar(Solver *solver, Row *row, Symbol sym, Float value) {
    Term *term;
    if (sym.id == 0) return;
    if ((term = cast(Term*)am_gettable(&row.terms, sym)) is null)
        term = cast(Term*)am_settable(solver, &row.terms, sym);
    if (nearzero(term.multiplier += value))
        am_delkey(&row.terms, &term.entry);
}

void am_addrow(Solver *solver, Row *row, const Row *other, Float multiplier) {
    Term *term = null;
    row.constant += other.constant*multiplier;
    while (am_nextentry(&other.terms, cast(Entry**)&term))
        am_addvar(solver, row, am_key(term), term.multiplier*multiplier);
}

void am_solvefor(Solver *solver, Row *row, Symbol entry, Symbol exit) {
    Term *term = cast(Term*)am_gettable(&row.terms, entry);
    Float reciprocal = 1.0f / term.multiplier;
    assert(entry.id != exit.id && !nearzero(term.multiplier));
    am_delkey(&row.terms, &term.entry);
    am_multiply(row, -reciprocal);
    if (exit.id != 0) am_addvar(solver, row, exit, reciprocal);
}

void am_substitute(Solver *solver, Row *row, Symbol entry, const Row *other) {
    Term *term = cast(Term*)am_gettable(&row.terms, entry);
    if (!term) return;
    am_delkey(&row.terms, &term.entry);
    am_addrow(solver, row, other, term.multiplier);
}


/* variables & constraints */

int am_variableid(Variable *var) { return var ? var.sym.id : -1; }
Float am_value(Variable *var) { return var ? var.value : 0.0f; }
void am_usevariable(Variable *var) { if (var) ++var.refcount; }

Variable *am_sym2var(Solver *solver, Symbol sym) {
    VarEntry *ve = cast(VarEntry*)am_gettable(&solver.vars, sym);
    assert(ve !is null);
    return ve.variable;
}

Variable* am_newvariable(Solver *solver) {
    Variable *var = cast(Variable*)alloc(solver, &solver.varpool);
    Symbol sym = am_newsymbol(solver, AM_EXTERNAL);
    VarEntry *ve = cast(VarEntry*)am_settable(solver, &solver.vars, sym);
    assert(ve.variable is null);
    memset(var, 0, (*var).sizeof);
    var.sym      = sym;
    var.refcount = 1;
    var.solver   = solver;
    ve.variable  = var;
    return var;
}

void am_delvariable(Variable *var) {
    if (var && --var.refcount <= 0) {
        Solver *solver = var.solver;
        VarEntry *e = cast(VarEntry*)am_gettable(&solver.vars, var.sym);
        assert(e !is null);
        am_delkey(&solver.vars, &e.entry);
        am_remove(var.constraint);
        am_free(&solver.varpool, var);
    }
}

Constraint* am_newconstraint(Solver *solver, Float strength) {
    Constraint *cons = cast(Constraint*)alloc(solver, &solver.conspool);
    memset(cons, 0, (*cons).sizeof);
    cons.solver   = solver;
    cons.strength = nearzero(strength) ? AM_REQUIRED : strength;
    am_initrow(&cons.expression);
    (cast(Entry*)(cons)).key.id = ++solver.constraint_count;
    (cast(Entry*)(cons)).key.type = AM_EXTERNAL;
    (cast(ConsEntry*)am_settable(solver, &solver.constraints, am_key(cons))).constraint = cons;
    return cons;
}

void am_delconstraint(Constraint *cons) {
    Solver *solver = cons ? cons.solver : null;
    Term *term = null;
    ConsEntry *ce;
    if (cons is null) return;
    am_remove(cons);
    ce = cast(ConsEntry*)am_gettable(&solver.constraints, am_key(cons));
    assert(ce !is null);
    am_delkey(&solver.constraints, &ce.entry);
    while (am_nextentry(&cons.expression.terms, cast(Entry**)&term))
        am_delvariable(am_sym2var(solver, am_key(term)));
    am_freerow(solver, &cons.expression);
    am_free(&solver.conspool, cons);
}

Constraint *am_cloneconstraint(Constraint *other, Float strength) {
    Constraint *cons;
    if (other is null) return null;
    cons = am_newconstraint(other.solver,
            nearzero(strength) ? other.strength : strength);
    am_mergeconstraint(cons, other, 1.0f);
    cons.relation = other.relation;
    return cons;
}

int am_mergeconstraint(Constraint *cons, Constraint *other, Float multiplier) {
    Term *term = null;
    if (cons is null || other is null || cons.marker.id != 0
            || cons.solver != other.solver) return AM_FAILED;
    if (cons.relation == AM_GREATEQUAL) multiplier = -multiplier;
    cons.expression.constant += other.expression.constant*multiplier;
    while (am_nextentry(&other.expression.terms, cast(Entry**)&term)) {
        am_usevariable(am_sym2var(cons.solver, am_key(term)));
        am_addvar(cons.solver, &cons.expression, am_key(term),
                term.multiplier*multiplier);
    }
    return AM_OK;
}

void am_resetconstraint(Constraint *cons) {
    Term *term = null;
    if (cons is null) return;
    am_remove(cons);
    cons.relation = 0;
    while (am_nextentry(&cons.expression.terms, cast(Entry**)&term))
        am_delvariable(am_sym2var(cons.solver, am_key(term)));
    am_resetrow(&cons.expression);
}

int am_addterm(Constraint *cons, Variable *var, Float multiplier = 1.0) {
    if (cons is null || var is null || cons.marker.id != 0 ||
            cons.solver != var.solver) return AM_FAILED;
    assert(var.sym.id != 0);
    assert(var.solver == cons.solver);
    if (cons.relation == AM_GREATEQUAL) multiplier = -multiplier;
    am_addvar(cons.solver, &cons.expression, var.sym, multiplier);
    am_usevariable(var);
    return AM_OK;
}

int am_addconstant(Constraint *cons, Float constant) {
    if (cons is null || cons.marker.id != 0) return AM_FAILED;
    if (cons.relation == AM_GREATEQUAL)
        cons.expression.constant -= constant;
    else
        cons.expression.constant += constant;
    return AM_OK;
}

int am_setrelation(Constraint *cons, int relation) {
    assert(relation >= AM_LESSEQUAL && relation <= AM_GREATEQUAL);
    if (cons is null || cons.marker.id != 0 || cons.relation != 0)
        return AM_FAILED;
    if (relation != AM_GREATEQUAL) am_multiply(&cons.expression, -1.0f);
    cons.relation = relation;
    return AM_OK;
}


// /* Cassowary algorithm */

int am_hasedit(Variable *var)
{
	return var !is null && var.constraint !is null;
}

int am_hasconstraint(Constraint *cons)
{
	return cons !is null && cons.marker.id != 0;
}

void am_autoupdate(Solver *solver, int auto_update)
{
	solver.auto_update = auto_update;
}

void am_infeasible(Solver *solver, Row *row) {
    if (am_isdummy(row.infeasible_next)) return;
    row.infeasible_next.id = solver.infeasible_rows.id;
    row.infeasible_next.type = AM_DUMMY;
    solver.infeasible_rows = am_key(row);
}

void am_markdirty(Solver *solver, Variable *var) {
    if (var.dirty_next.type == AM_DUMMY) return;
    var.dirty_next.id = solver.dirty_vars.id;
    var.dirty_next.type = AM_DUMMY;
    solver.dirty_vars = var.sym;
}

void am_substitute_rows(Solver *solver, Symbol var, Row *expr) {
    Row *row = null;
    while (am_nextentry(&solver.rows, cast(Entry**)&row)) {
        am_substitute(solver, row, var, expr);
        if (am_isexternal(am_key(row)))
            am_markdirty(solver, am_sym2var(solver, am_key(row)));
        else if (row.constant < 0.0f)
            am_infeasible(solver, row);
    }
    am_substitute(solver, &solver.objective, var, expr);
}

int am_getrow(Solver *solver, Symbol sym, Row *dst) {
    Row *row = cast(Row*)am_gettable(&solver.rows, sym);
    (cast(Entry*)(dst)).key = Symbol();
    if (row is null) return AM_FAILED;
    am_delkey(&solver.rows, &row.entry);
    dst.constant   = row.constant;
    dst.terms      = row.terms;
    return AM_OK;
}

int am_putrow(Solver *solver, Symbol sym, /*const*/ Row *src) {
    Row *row = cast(Row*)am_settable(solver, &solver.rows, sym);
    row.constant = src.constant;
    row.terms    = src.terms;
    return AM_OK;
}

void am_mergerow(Solver *solver, Row *row, Symbol var, Float multiplier) @nogc nothrow
{
    Row *oldrow = cast(Row*)am_gettable(&solver.rows, var);
    if (oldrow) am_addrow(solver, row, oldrow, multiplier);
    else am_addvar(solver, row, var, multiplier);
}

int am_optimize(Solver *solver, Row *objective) {
    for (;;) {
        Symbol enter = Symbol(), exit = Symbol();
        Float r, min_ratio = Float.max;
        Row tmp = void;
		Row *row = null;
        Term *term = null;

        assert(solver.infeasible_rows.id == 0);
        while (am_nextentry(&objective.terms, cast(Entry**)&term)) {
            if (!am_isdummy(am_key(term)) && term.multiplier < 0.0f)
            { enter = am_key(term); break; }
        }
        if (enter.id == 0) return AM_OK;

        while (am_nextentry(&solver.rows, cast(Entry**)&row)) {
            term = cast(Term*)am_gettable(&row.terms, enter);
            if (term is null || !am_ispivotable(am_key(row))
                    || term.multiplier > 0.0f) continue;
            r = -row.constant / term.multiplier;
            if (r < min_ratio || (approx(r, min_ratio)
                        && am_key(row).id < exit.id))
                min_ratio = r, exit = am_key(row);
        }
        assert(exit.id != 0);
        if (exit.id == 0) return AM_FAILED;

        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, enter, exit);
        am_substitute_rows(solver, enter, &tmp);
        if (objective != &solver.objective)
            am_substitute(solver, objective, enter, &tmp);
        am_putrow(solver, enter, &tmp);
    }
}

Row am_makerow(Solver *solver, Constraint *cons) {
    Term *term = null;
    Row row;
    am_initrow(&row);
    row.constant = cons.expression.constant;
    while (am_nextentry(&cons.expression.terms, cast(Entry**)&term)) {
        am_markdirty(solver, am_sym2var(solver, am_key(term)));
        am_mergerow(solver, &row, am_key(term), term.multiplier);
    }
    if (cons.relation != AM_EQUAL) {
        initsymbol(solver, &cons.marker, AM_SLACK);
        am_addvar(solver, &row, cons.marker, -1.0f);
        if (cons.strength < AM_REQUIRED) {
            initsymbol(solver, &cons.other, AM_ERROR);
            am_addvar(solver, &row, cons.other, 1.0f);
            am_addvar(solver, &solver.objective, cons.other, cons.strength);
        }
    }
    else if (cons.strength >= AM_REQUIRED) {
        initsymbol(solver, &cons.marker, AM_DUMMY);
        am_addvar(solver, &row, cons.marker, 1.0f);
    }
    else {
        initsymbol(solver, &cons.marker, AM_ERROR);
        initsymbol(solver, &cons.other,  AM_ERROR);
        am_addvar(solver, &row, cons.marker, -1.0f);
        am_addvar(solver, &row, cons.other,   1.0f);
        am_addvar(solver, &solver.objective, cons.marker, cons.strength);
        am_addvar(solver, &solver.objective, cons.other,  cons.strength);
    }
    if (row.constant < 0.0f) am_multiply(&row, -1.0f);
    return row;
}

void am_remove_errors(Solver *solver, Constraint *cons) @nogc nothrow
{
    if (am_iserror(cons.marker))
        am_mergerow(solver, &solver.objective, cons.marker, -cons.strength);
    if (am_iserror(cons.other))
        am_mergerow(solver, &solver.objective, cons.other, -cons.strength);
    if (am_isconstant(&solver.objective))
        solver.objective.constant = 0.0f;
    cons.marker = cons.other = Symbol();
}

int am_add_with_artificial(Solver *solver, Row *row, Constraint *cons) {
    Symbol a = am_newsymbol(solver, AM_SLACK);
    Term *term = null;
    Row tmp;
    int ret;
    --solver.symbol_count; /* artificial variable will be removed */
    am_initrow(&tmp);
    am_addrow(solver, &tmp, row, 1.0f);
    am_putrow(solver, a, row);
    am_initrow(row), row = null; /* row is useless */
    am_optimize(solver, &tmp);
    ret = nearzero(tmp.constant) ? AM_OK : AM_UNBOUND;
    am_freerow(solver, &tmp);
    if (am_getrow(solver, a, &tmp) == AM_OK) {
        Symbol entry = Symbol();
        if (am_isconstant(&tmp)) { am_freerow(solver, &tmp); return ret; }
        while (am_nextentry(&tmp.terms, cast(Entry**)&term))
            if (am_ispivotable(am_key(term))) { entry = am_key(term); break; }
        if (entry.id == 0) { am_freerow(solver, &tmp); return AM_UNBOUND; }
        am_solvefor(solver, &tmp, entry, a);
        am_substitute_rows(solver, entry, &tmp);
        am_putrow(solver, entry, &tmp);
    }
    while (am_nextentry(&solver.rows, cast(Entry**)&row)) {
        term = cast(Term*)am_gettable(&row.terms, a);
        if (term) am_delkey(&row.terms, &term.entry);
    }
    term = cast(Term*)am_gettable(&solver.objective.terms, a);
    if (term) am_delkey(&solver.objective.terms, &term.entry);
    if (ret != AM_OK) am_remove(cons);
    return ret;
}

int am_try_addrow(Solver *solver, Row *row, Constraint *cons) {
    Symbol subject = Symbol();
    Term *term = null;
    while (am_nextentry(&row.terms, cast(Entry**)&term))
        if (am_isexternal(am_key(term))) { subject = am_key(term); break; }
    if (subject.id == 0 && am_ispivotable(cons.marker)) {
        Term *mterm = cast(Term*)am_gettable(&row.terms, cons.marker);
        if (mterm.multiplier < 0.0f) subject = cons.marker;
    }
    if (subject.id == 0 && am_ispivotable(cons.other)) {
        Term *mterm = cast(Term*)am_gettable(&row.terms, cons.other);
        if (mterm.multiplier < 0.0f) subject = cons.other;
    }
    if (subject.id == 0) {
        while (am_nextentry(&row.terms, cast(Entry**)&term))
            if (!am_isdummy(am_key(term))) break;
        if (term is null) {
            if (nearzero(row.constant))
                subject = cons.marker;
            else {
                am_freerow(solver, row);
                return AM_UNSATISFIED;
            }
        }
    }
    if (subject.id == 0)
        return am_add_with_artificial(solver, row, cons);
    am_solvefor(solver, row, subject, Symbol());
    am_substitute_rows(solver, subject, row);
    am_putrow(solver, subject, row);
    return AM_OK;
}

Symbol am_get_leaving_row(Solver *solver, Symbol marker) {
    Symbol first = Symbol(), second = Symbol(), third = Symbol();
    Float r1 = Float.max, r2 = Float.max;
    Row *row = null;
    while (am_nextentry(&solver.rows, cast(Entry**)&row)) {
        Term *term = cast(Term*)am_gettable(&row.terms, marker);
        if (term is null) continue;
        if (am_isexternal(am_key(row))) third = am_key(row);
        else if (term.multiplier < 0.0f) {
            Float r = -row.constant / term.multiplier;
            if (r < r1) r1 = r, first = am_key(row);
        }
        else {
            Float r = row.constant / term.multiplier;
            if (r < r2) r2 = r, second = am_key(row);
        }
    }
    return first.id ? first : second.id ? second : third;
}

void am_delta_edit_constant(Solver *solver, Float delta, Constraint *cons) {
    Row *row;
    if ((row = cast(Row*)am_gettable(&solver.rows, cons.marker)) !is null)
    { if ((row.constant -= delta) < 0.0f) am_infeasible(solver, row); return; }
    if ((row = cast(Row*)am_gettable(&solver.rows, cons.other)) !is null)
    { if ((row.constant += delta) < 0.0f) am_infeasible(solver, row); return; }
    while (am_nextentry(&solver.rows, cast(Entry**)&row)) {
        Term *term = cast(Term*)am_gettable(&row.terms, cons.marker);
        if (term is null) continue;
        row.constant += term.multiplier*delta;
        if (am_isexternal(am_key(row)))
            am_markdirty(solver, am_sym2var(solver, am_key(row)));
        else if (row.constant < 0.0f)
            am_infeasible(solver, row);
    }
}

void am_dual_optimize(Solver *solver) {
    while (solver.infeasible_rows.id != 0) {
        Row tmp = void;
		Row *row =
            cast(Row*)am_gettable(&solver.rows, solver.infeasible_rows);
        Symbol enter = Symbol(), exit = am_key(row), curr;
        Term *objterm = void;
		Term *term = null;
        Float r, min_ratio = Float.max;
        solver.infeasible_rows = row.infeasible_next;
        row.infeasible_next = Symbol();
        if (row.constant >= 0.0f) continue;
        while (am_nextentry(&row.terms, cast(Entry**)&term)) {
            if (am_isdummy(curr = am_key(term)) || term.multiplier <= 0.0f)
                continue;
            objterm = cast(Term*)am_gettable(&solver.objective.terms, curr);
            r = objterm ? objterm.multiplier / term.multiplier : 0.0f;
            if (min_ratio > r) min_ratio = r, enter = curr;
        }
        assert(enter.id != 0);
        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, enter, exit);
        am_substitute_rows(solver, enter, &tmp);
        am_putrow(solver, enter, &tmp);
    }
}

void *am_default_allocf(void *ud, void *ptr, size_t nsize, size_t osize) {
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

Solver *am_newsolver(am_Allocf allocf, void *ud) {
    Solver *solver;
    if (allocf is null) allocf = &am_default_allocf;
    if ((solver = cast(Solver*)allocf(ud, null, Solver.sizeof, 0)) is null)
        return null;
    memset(solver, 0, (*solver).sizeof);
    solver.allocf = allocf;
    solver.ud     = ud;
    am_initrow(&solver.objective);
    am_inittable(&solver.vars, VarEntry.sizeof);
    am_inittable(&solver.constraints, ConsEntry.sizeof);
    am_inittable(&solver.rows, Row.sizeof);
    solver.varpool  = MemPool(Variable.sizeof);
    solver.conspool = MemPool(Constraint.sizeof);
    return solver;
}

void am_delsolver(Solver *solver) {
    ConsEntry *ce = null;
    Row *row = null;
    while (am_nextentry(&solver.constraints, cast(Entry**)&ce))
        am_freerow(solver, &ce.constraint.expression);
    while (am_nextentry(&solver.rows, cast(Entry**)&row))
        am_freerow(solver, row);
    am_freerow(solver, &solver.objective);
    am_freetable(solver, &solver.vars);
    am_freetable(solver, &solver.constraints);
    am_freetable(solver, &solver.rows);
    freepool(solver, &solver.varpool);
    freepool(solver, &solver.conspool);
    solver.allocf(solver.ud, solver, 0, (*solver).sizeof);
}

void am_resetsolver(Solver *solver, int clear_constraints) {
    Entry *entry = null;
    if (!solver.auto_update) am_updatevars(solver);
    while (am_nextentry(&solver.vars, &entry)) {
        Constraint **cons = &(cast(VarEntry*)entry).variable.constraint;
        am_remove(*cons);
        *cons = null;
    }
    assert(nearzero(solver.objective.constant));
    assert(solver.infeasible_rows.id == 0);
    assert(solver.dirty_vars.id == 0);
    if (!clear_constraints) return;
    am_resetrow(&solver.objective);
    while (am_nextentry(&solver.constraints, &entry)) {
        Constraint *cons = (cast(ConsEntry*)entry).constraint;
        if (cons.marker.id == 0) continue;
        cons.marker = cons.other = Symbol();
    }
    while (am_nextentry(&solver.rows, &entry)) {
        am_delkey(&solver.rows, entry);
        am_freerow(solver, cast(Row*)entry);
    }
}

void am_updatevars(Solver *solver) {
    while (solver.dirty_vars.id != 0) {
        Variable *var = am_sym2var(solver, solver.dirty_vars);
        Row *row = cast(Row*)am_gettable(&solver.rows, var.sym);
        solver.dirty_vars = var.dirty_next;
        var.dirty_next = Symbol();
        var.value = row ? row.constant : 0.0f;
    }
}

int am_add(Constraint *cons) {
    Solver *solver = cons ? cons.solver : null;
    int ret, oldsym = solver ? solver.symbol_count : 0;
    Row row;
    if (solver is null || cons.marker.id != 0) return AM_FAILED;
    row = am_makerow(solver, cons);
    if ((ret = am_try_addrow(solver, &row, cons)) != AM_OK) {
        am_remove_errors(solver, cons);
        solver.symbol_count = oldsym;
    }
    else {
        am_optimize(solver, &solver.objective);
        if (solver.auto_update) am_updatevars(solver);
    }
    return ret;
}

void am_remove(Constraint *cons) @nogc nothrow
{
    Solver *solver;
    Symbol marker;
    Row tmp;
    if (cons is null || cons.marker.id == 0) return;
    solver = cons.solver, marker = cons.marker;
    am_remove_errors(solver, cons);
    if (am_getrow(solver, marker, &tmp) != AM_OK) {
        Symbol exit = am_get_leaving_row(solver, marker);
        assert(exit.id != 0);
        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, marker, exit);
        am_substitute_rows(solver, marker, &tmp);
    }
    am_freerow(solver, &tmp);
    am_optimize(solver, &solver.objective);
    if (solver.auto_update) am_updatevars(solver);
}

int am_setstrength(Constraint *cons, Float strength)
{
    if (cons is null) return AM_FAILED;
    strength = nearzero(strength) ? AM_REQUIRED : strength;
    if (cons.strength == strength) return AM_OK;
    if (cons.strength >= AM_REQUIRED || strength >= AM_REQUIRED)
    { am_remove(cons), cons.strength = strength; return am_add(cons); }
    if (cons.marker.id != 0) {
        Solver *solver = cons.solver;
        Float diff = strength - cons.strength;
        am_mergerow(solver, &solver.objective, cons.marker, diff);
        am_mergerow(solver, &solver.objective, cons.other,  diff);
        am_optimize(solver, &solver.objective);
        if (solver.auto_update) am_updatevars(solver);
    }
    cons.strength = strength;
    return AM_OK;
}

int am_addedit(Variable *var, Float strength) {
    Solver *solver = var ? var.solver : null;
    Constraint *cons;
    if (var is null || var.constraint !is null) return AM_FAILED;
    assert(var.sym.id != 0);
    if (strength > AM_STRONG) strength = AM_STRONG;
    cons = am_newconstraint(solver, strength);
    am_setrelation(cons, AM_EQUAL);
    am_addterm(cons, var, 1.0f); /* var must have positive signture */
    am_addconstant(cons, -var.value);
    if (am_add(cons) != AM_OK) assert(0);
    var.constraint = cons;
    var.edit_value = var.value;
    return AM_OK;
}

void am_deledit(Variable *var) {
    if (var is null || var.constraint is null) return;
    am_delconstraint(var.constraint);
    var.constraint = null;
    var.edit_value = 0.0f;
}

void am_suggest(Variable *var, Float value) {
    Solver *solver = var ? var.solver : null;
    Float delta;
    if (var is null) return;
    if (var.constraint is null) {
        am_addedit(var, AM_MEDIUM);
        assert(var.constraint !is null);
    }
    delta = value - var.edit_value;
    var.edit_value = value;
    am_delta_edit_constant(solver, delta, var.constraint);
    am_dual_optimize(solver);
    if (solver.auto_update) am_updatevars(solver);
}

// AM_NS_END


// #endif /* AM_IMPLEMENTATION */

// /* cc: flags+='-shared -O2 -DAM_IMPLEMENTATION -xc'
//    unixcc: output='amoeba.so'
//    win32cc: output='amoeba.dll' */

