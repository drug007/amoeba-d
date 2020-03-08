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

enum AM_REQUIRED    = cast(am_Float)1000000000;
enum AM_STRONG      = cast(am_Float)1000000;
enum AM_MEDIUM      = cast(am_Float)1000;
enum AM_WEAK        = cast(am_Float)1;

version (AM_USE_FLOAT)
{
	alias am_Float = float;
	enum AM_FLOAT_EPS = 1e-4f;
}
else
{
	alias am_Float = double;
	enum AM_FLOAT_EPS = 1e-6;
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

struct am_Symbol {
	import mir.bitmanip : bitfields;
	mixin(bitfields!(
		uint, "id",    30,
		uint, "type",   2,));
	debug string label;
}

struct am_MemPool {
	size_t size;
	void*  freed;
	void*  pages;

	this(size_t size) @nogc nothrow
	{
		this.size  = size;
		assert(size > (void*).sizeof && size < AM_POOLSIZE/4);
	}
}

struct am_Entry {
	int       next;
	am_Symbol key;
}

struct am_Table {
	size_t    size;
	size_t    count;
	size_t    entry_size;
	size_t    lastfree;
	am_Entry *hash;
}

struct am_VarEntry {
	am_Entry     entry;
	am_Variable *variable;
}

struct am_ConsEntry {
	am_Entry       entry;
	am_Constraint *constraint;
}

struct am_Term {
	am_Entry entry;
	am_Float multiplier;
}

struct am_Row {
	am_Entry  entry;
	am_Symbol infeasible_next;
	am_Table  terms;
	am_Float  constant;
}

struct am_Variable {
	am_Symbol      sym;
	am_Symbol      dirty_next;
	uint           refcount;
	am_Solver     *solver;
	am_Constraint *constraint;
	am_Float       edit_value;
	am_Float       value;
}

struct am_Constraint {
	am_Row     expression;
	am_Symbol  marker;
	am_Symbol  other;
	int        relation;
	am_Solver *solver;
	am_Float   strength;
}

struct am_Solver {
	am_Allocf  allocf;
	void      *ud;
	am_Row     objective;
	am_Table   vars;            /* symbol . VarEntry */
	am_Table   constraints;     /* symbol . ConsEntry */
	am_Table   rows;            /* symbol . Row */
	am_MemPool varpool;
	am_MemPool conspool;
	uint       symbol_count;
	uint       constraint_count;
	uint       auto_update;
	am_Symbol  infeasible_rows;
	am_Symbol  dirty_vars;
}

/* utils */

int am_approx(am_Float a, am_Float b) @nogc nothrow
{
	return a > b ? (a - b < AM_FLOAT_EPS) : (b - a < AM_FLOAT_EPS);
}

int am_nearzero(am_Float a) @nogc nothrow
{
	return am_approx(a, 0.0f);
}

void am_initsymbol(am_Solver *solver, am_Symbol *sym, int type)
{
	if (sym.id == 0)
		*sym = am_newsymbol(solver, type);
}

void am_freepool(am_Solver *solver, am_MemPool *pool) {
    const size_t offset = AM_POOLSIZE - (void*).sizeof;
    while (pool.pages !is null) {
        void *next = *cast(void**)(cast(char*)pool.pages + offset);
        solver.allocf(solver.ud, pool.pages, 0, AM_POOLSIZE);
        pool.pages = next;
    }
    *pool = am_MemPool(pool.size);
}

void *am_alloc(am_Solver *solver, am_MemPool *pool) {
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

void am_free(am_MemPool *pool, void *obj) {
    *cast(void**)obj = pool.freed;
    pool.freed = obj;
}

am_Symbol am_newsymbol(am_Solver *solver, int type) {
    am_Symbol sym;
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
	auto am_key(E)(E entry) { return (cast(am_Entry*)(entry)).key; }

	// #define am_offset(lhs, rhs) ((int)((char*)(lhs) - (char*)(rhs)))
	auto am_offset(L, R)(L lhs, R rhs) { return cast(int)(cast(char*)(lhs) - cast(char*)(rhs)); }
	// #define am_index(h, i)      ((am_Entry*)((char*)(h) + (i)))
	auto am_index(H, I)(H h, I i) { return cast(am_Entry*)(cast(char*)(h) + (i)); }
}

void am_delkey(am_Table *t, am_Entry *entry)
{
	entry.key = am_Symbol(), --t.count;
}

void am_inittable(am_Table *t, size_t entry_size)
{
	memset(t, 0, (*t).sizeof), t.entry_size = entry_size;
}

am_Entry *am_mainposition(const am_Table *t, am_Symbol key) @nogc nothrow
{
	return am_index(t.hash, (key.id & (t.size - 1))*t.entry_size);
}

void am_resettable(am_Table *t)
{
	t.count = 0;
	memset(t.hash, 0, t.lastfree = t.size * t.entry_size);
}

size_t am_hashsize(am_Table *t, size_t len) {
    size_t newsize = AM_MIN_HASHSIZE;
    const size_t max_size = (AM_MAX_SIZET / 2) / t.entry_size;
    while (newsize < max_size && newsize < len)
        newsize <<= 1;
    assert((newsize & (newsize - 1)) == 0);
    return newsize < len ? 0 : newsize;
}

void am_freetable(am_Solver *solver, am_Table *t)
{
    size_t size = t.size*t.entry_size;
    if (size) solver.allocf(solver.ud, t.hash, 0, size);
    am_inittable(t, t.entry_size);
}

size_t am_resizetable(am_Solver *solver, am_Table *t, size_t len) {
    size_t i, oldsize = t.size * t.entry_size;
    am_Table nt = *t;
    nt.size = am_hashsize(t, len);
    nt.lastfree = nt.size*nt.entry_size;
    nt.hash = cast(am_Entry*)solver.allocf(solver.ud, null, nt.lastfree, 0);
    memset(nt.hash, 0, nt.size*nt.entry_size);
    for (i = 0; i < oldsize; i += nt.entry_size) {
        am_Entry *e = am_index(t.hash, i);
        if (e.key.id != 0) {
            am_Entry *ne = am_newkey(solver, &nt, e.key);
            if (t.entry_size > am_Entry.sizeof)
                memcpy(ne + 1, e + 1, t.entry_size-am_Entry.sizeof);
        }
    }
    if (oldsize) solver.allocf(solver.ud, t.hash, 0, oldsize);
    *t = nt;
    return t.size;
}
am_Entry *am_newkey(am_Solver *solver, am_Table *t, am_Symbol key) {
    if (t.size == 0) am_resizetable(solver, t, AM_MIN_HASHSIZE);
    for (;;) {
        am_Entry *mp = am_mainposition(t, key);
        if (mp.key.id != 0) {
            am_Entry *f = null;
			am_Entry *othern = void;
            while (t.lastfree > 0) {
                am_Entry *e = am_index(t.hash, t.lastfree -= t.entry_size);
                if (e.key.id == 0 && e.next == 0)  { f = e; break; }
            }
            if (!f) { am_resizetable(solver, t, t.count*2); continue; }
            assert(f.key.id == 0);
            othern = am_mainposition(t, mp.key);
            if (othern != mp) {
                am_Entry *next;
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

am_Entry *am_gettable(const am_Table *t, am_Symbol key) @nogc nothrow
{
    am_Entry *e;
    if (t.size == 0 || key.id == 0) return null;
    e = am_mainposition(t, key);
    for (; e.key.id != key.id; e = am_index(e, e.next))
        if (e.next == 0) return null;
    return e;
}

am_Entry *am_settable(am_Solver *solver, am_Table *t, am_Symbol key) {
    am_Entry *e;
    assert(key.id != 0);
    if ((e = cast(am_Entry*)am_gettable(t, key)) !is null) return e;
    e = am_newkey(solver, t, key);
    if (t.entry_size > am_Entry.sizeof)
        memset(e + 1, 0, t.entry_size-am_Entry.sizeof);
    ++t.count;
    return e;
}

int am_nextentry(const(am_Table) *t, am_Entry **pentry) {
    size_t i = *pentry ? am_offset(*pentry, t.hash) + t.entry_size : 0;
    size_t size = t.size*t.entry_size;
    for (; i < size; i += t.entry_size) {
        am_Entry *e = am_index(t.hash, i);
        if (e.key.id != 0) { *pentry = e; return 1; }
    }
    *pentry = null;
    return 0;
}


/* expression (row) */

int am_isconstant(am_Row *row)
{
	return row.terms.count == 0;
}

void am_freerow(am_Solver *solver, am_Row *row)
{
	am_freetable(solver, &row.terms);
}

void am_resetrow(am_Row *row)
{
	row.constant = 0.0f;
	am_resettable(&row.terms);
}

void am_initrow(am_Row *row) {
    // am_key(row) = am_Symbol();
	(cast(am_Entry*)(row)).key  = am_Symbol();
    row.infeasible_next = am_Symbol();
    row.constant = 0.0f;
    am_inittable(&row.terms, am_Term.sizeof);
}

void am_multiply(am_Row *row, am_Float multiplier) {
    am_Term *term = null;
    row.constant *= multiplier;
    while (am_nextentry(&row.terms, cast(am_Entry**)&term))
        term.multiplier *= multiplier;
}

void am_addvar(am_Solver *solver, am_Row *row, am_Symbol sym, am_Float value) {
    am_Term *term;
    if (sym.id == 0) return;
    if ((term = cast(am_Term*)am_gettable(&row.terms, sym)) is null)
        term = cast(am_Term*)am_settable(solver, &row.terms, sym);
    if (am_nearzero(term.multiplier += value))
        am_delkey(&row.terms, &term.entry);
}

void am_addrow(am_Solver *solver, am_Row *row, const am_Row *other, am_Float multiplier) {
    am_Term *term = null;
    row.constant += other.constant*multiplier;
    while (am_nextentry(&other.terms, cast(am_Entry**)&term))
        am_addvar(solver, row, am_key(term), term.multiplier*multiplier);
}

void am_solvefor(am_Solver *solver, am_Row *row, am_Symbol entry, am_Symbol exit) {
    am_Term *term = cast(am_Term*)am_gettable(&row.terms, entry);
    am_Float reciprocal = 1.0f / term.multiplier;
    assert(entry.id != exit.id && !am_nearzero(term.multiplier));
    am_delkey(&row.terms, &term.entry);
    am_multiply(row, -reciprocal);
    if (exit.id != 0) am_addvar(solver, row, exit, reciprocal);
}

void am_substitute(am_Solver *solver, am_Row *row, am_Symbol entry, const am_Row *other) {
    am_Term *term = cast(am_Term*)am_gettable(&row.terms, entry);
    if (!term) return;
    am_delkey(&row.terms, &term.entry);
    am_addrow(solver, row, other, term.multiplier);
}


/* variables & constraints */

int am_variableid(am_Variable *var) { return var ? var.sym.id : -1; }
am_Float am_value(am_Variable *var) { return var ? var.value : 0.0f; }
void am_usevariable(am_Variable *var) { if (var) ++var.refcount; }

am_Variable *am_sym2var(am_Solver *solver, am_Symbol sym) {
    am_VarEntry *ve = cast(am_VarEntry*)am_gettable(&solver.vars, sym);
    assert(ve !is null);
    return ve.variable;
}

am_Variable* am_newvariable(am_Solver *solver) {
    am_Variable *var = cast(am_Variable*)am_alloc(solver, &solver.varpool);
    am_Symbol sym = am_newsymbol(solver, AM_EXTERNAL);
    am_VarEntry *ve = cast(am_VarEntry*)am_settable(solver, &solver.vars, sym);
    assert(ve.variable is null);
    memset(var, 0, (*var).sizeof);
    var.sym      = sym;
    var.refcount = 1;
    var.solver   = solver;
    ve.variable  = var;
    return var;
}

void am_delvariable(am_Variable *var) {
    if (var && --var.refcount <= 0) {
        am_Solver *solver = var.solver;
        am_VarEntry *e = cast(am_VarEntry*)am_gettable(&solver.vars, var.sym);
        assert(e !is null);
        am_delkey(&solver.vars, &e.entry);
        am_remove(var.constraint);
        am_free(&solver.varpool, var);
    }
}

am_Constraint* am_newconstraint(am_Solver *solver, am_Float strength) {
    am_Constraint *cons = cast(am_Constraint*)am_alloc(solver, &solver.conspool);
    memset(cons, 0, (*cons).sizeof);
    cons.solver   = solver;
    cons.strength = am_nearzero(strength) ? AM_REQUIRED : strength;
    am_initrow(&cons.expression);
    (cast(am_Entry*)(cons)).key.id = ++solver.constraint_count;
    (cast(am_Entry*)(cons)).key.type = AM_EXTERNAL;
    (cast(am_ConsEntry*)am_settable(solver, &solver.constraints, am_key(cons))).constraint = cons;
    return cons;
}

void am_delconstraint(am_Constraint *cons) {
    am_Solver *solver = cons ? cons.solver : null;
    am_Term *term = null;
    am_ConsEntry *ce;
    if (cons is null) return;
    am_remove(cons);
    ce = cast(am_ConsEntry*)am_gettable(&solver.constraints, am_key(cons));
    assert(ce !is null);
    am_delkey(&solver.constraints, &ce.entry);
    while (am_nextentry(&cons.expression.terms, cast(am_Entry**)&term))
        am_delvariable(am_sym2var(solver, am_key(term)));
    am_freerow(solver, &cons.expression);
    am_free(&solver.conspool, cons);
}

am_Constraint *am_cloneconstraint(am_Constraint *other, am_Float strength) {
    am_Constraint *cons;
    if (other is null) return null;
    cons = am_newconstraint(other.solver,
            am_nearzero(strength) ? other.strength : strength);
    am_mergeconstraint(cons, other, 1.0f);
    cons.relation = other.relation;
    return cons;
}

int am_mergeconstraint(am_Constraint *cons, am_Constraint *other, am_Float multiplier) {
    am_Term *term = null;
    if (cons is null || other is null || cons.marker.id != 0
            || cons.solver != other.solver) return AM_FAILED;
    if (cons.relation == AM_GREATEQUAL) multiplier = -multiplier;
    cons.expression.constant += other.expression.constant*multiplier;
    while (am_nextentry(&other.expression.terms, cast(am_Entry**)&term)) {
        am_usevariable(am_sym2var(cons.solver, am_key(term)));
        am_addvar(cons.solver, &cons.expression, am_key(term),
                term.multiplier*multiplier);
    }
    return AM_OK;
}

void am_resetconstraint(am_Constraint *cons) {
    am_Term *term = null;
    if (cons is null) return;
    am_remove(cons);
    cons.relation = 0;
    while (am_nextentry(&cons.expression.terms, cast(am_Entry**)&term))
        am_delvariable(am_sym2var(cons.solver, am_key(term)));
    am_resetrow(&cons.expression);
}

int am_addterm(am_Constraint *cons, am_Variable *var, am_Float multiplier = 1.0) {
    if (cons is null || var is null || cons.marker.id != 0 ||
            cons.solver != var.solver) return AM_FAILED;
    assert(var.sym.id != 0);
    assert(var.solver == cons.solver);
    if (cons.relation == AM_GREATEQUAL) multiplier = -multiplier;
    am_addvar(cons.solver, &cons.expression, var.sym, multiplier);
    am_usevariable(var);
    return AM_OK;
}

int am_addconstant(am_Constraint *cons, am_Float constant) {
    if (cons is null || cons.marker.id != 0) return AM_FAILED;
    if (cons.relation == AM_GREATEQUAL)
        cons.expression.constant -= constant;
    else
        cons.expression.constant += constant;
    return AM_OK;
}

int am_setrelation(am_Constraint *cons, int relation) {
    assert(relation >= AM_LESSEQUAL && relation <= AM_GREATEQUAL);
    if (cons is null || cons.marker.id != 0 || cons.relation != 0)
        return AM_FAILED;
    if (relation != AM_GREATEQUAL) am_multiply(&cons.expression, -1.0f);
    cons.relation = relation;
    return AM_OK;
}


// /* Cassowary algorithm */

int am_hasedit(am_Variable *var)
{
	return var !is null && var.constraint !is null;
}

int am_hasconstraint(am_Constraint *cons)
{
	return cons !is null && cons.marker.id != 0;
}

void am_autoupdate(am_Solver *solver, int auto_update)
{
	solver.auto_update = auto_update;
}

void am_infeasible(am_Solver *solver, am_Row *row) {
    if (am_isdummy(row.infeasible_next)) return;
    row.infeasible_next.id = solver.infeasible_rows.id;
    row.infeasible_next.type = AM_DUMMY;
    solver.infeasible_rows = am_key(row);
}

void am_markdirty(am_Solver *solver, am_Variable *var) {
    if (var.dirty_next.type == AM_DUMMY) return;
    var.dirty_next.id = solver.dirty_vars.id;
    var.dirty_next.type = AM_DUMMY;
    solver.dirty_vars = var.sym;
}

void am_substitute_rows(am_Solver *solver, am_Symbol var, am_Row *expr) {
    am_Row *row = null;
    while (am_nextentry(&solver.rows, cast(am_Entry**)&row)) {
        am_substitute(solver, row, var, expr);
        if (am_isexternal(am_key(row)))
            am_markdirty(solver, am_sym2var(solver, am_key(row)));
        else if (row.constant < 0.0f)
            am_infeasible(solver, row);
    }
    am_substitute(solver, &solver.objective, var, expr);
}

int am_getrow(am_Solver *solver, am_Symbol sym, am_Row *dst) {
    am_Row *row = cast(am_Row*)am_gettable(&solver.rows, sym);
    (cast(am_Entry*)(dst)).key = am_Symbol();
    if (row is null) return AM_FAILED;
    am_delkey(&solver.rows, &row.entry);
    dst.constant   = row.constant;
    dst.terms      = row.terms;
    return AM_OK;
}

int am_putrow(am_Solver *solver, am_Symbol sym, /*const*/ am_Row *src) {
    am_Row *row = cast(am_Row*)am_settable(solver, &solver.rows, sym);
    row.constant = src.constant;
    row.terms    = src.terms;
    return AM_OK;
}

void am_mergerow(am_Solver *solver, am_Row *row, am_Symbol var, am_Float multiplier) @nogc nothrow
{
    am_Row *oldrow = cast(am_Row*)am_gettable(&solver.rows, var);
    if (oldrow) am_addrow(solver, row, oldrow, multiplier);
    else am_addvar(solver, row, var, multiplier);
}

int am_optimize(am_Solver *solver, am_Row *objective) {
    for (;;) {
        am_Symbol enter = am_Symbol(), exit = am_Symbol();
        am_Float r, min_ratio = am_Float.max;
        am_Row tmp = void;
		am_Row *row = null;
        am_Term *term = null;

        assert(solver.infeasible_rows.id == 0);
        while (am_nextentry(&objective.terms, cast(am_Entry**)&term)) {
            if (!am_isdummy(am_key(term)) && term.multiplier < 0.0f)
            { enter = am_key(term); break; }
        }
        if (enter.id == 0) return AM_OK;

        while (am_nextentry(&solver.rows, cast(am_Entry**)&row)) {
            term = cast(am_Term*)am_gettable(&row.terms, enter);
            if (term is null || !am_ispivotable(am_key(row))
                    || term.multiplier > 0.0f) continue;
            r = -row.constant / term.multiplier;
            if (r < min_ratio || (am_approx(r, min_ratio)
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

am_Row am_makerow(am_Solver *solver, am_Constraint *cons) {
    am_Term *term = null;
    am_Row row;
    am_initrow(&row);
    row.constant = cons.expression.constant;
    while (am_nextentry(&cons.expression.terms, cast(am_Entry**)&term)) {
        am_markdirty(solver, am_sym2var(solver, am_key(term)));
        am_mergerow(solver, &row, am_key(term), term.multiplier);
    }
    if (cons.relation != AM_EQUAL) {
        am_initsymbol(solver, &cons.marker, AM_SLACK);
        am_addvar(solver, &row, cons.marker, -1.0f);
        if (cons.strength < AM_REQUIRED) {
            am_initsymbol(solver, &cons.other, AM_ERROR);
            am_addvar(solver, &row, cons.other, 1.0f);
            am_addvar(solver, &solver.objective, cons.other, cons.strength);
        }
    }
    else if (cons.strength >= AM_REQUIRED) {
        am_initsymbol(solver, &cons.marker, AM_DUMMY);
        am_addvar(solver, &row, cons.marker, 1.0f);
    }
    else {
        am_initsymbol(solver, &cons.marker, AM_ERROR);
        am_initsymbol(solver, &cons.other,  AM_ERROR);
        am_addvar(solver, &row, cons.marker, -1.0f);
        am_addvar(solver, &row, cons.other,   1.0f);
        am_addvar(solver, &solver.objective, cons.marker, cons.strength);
        am_addvar(solver, &solver.objective, cons.other,  cons.strength);
    }
    if (row.constant < 0.0f) am_multiply(&row, -1.0f);
    return row;
}

void am_remove_errors(am_Solver *solver, am_Constraint *cons) @nogc nothrow
{
    if (am_iserror(cons.marker))
        am_mergerow(solver, &solver.objective, cons.marker, -cons.strength);
    if (am_iserror(cons.other))
        am_mergerow(solver, &solver.objective, cons.other, -cons.strength);
    if (am_isconstant(&solver.objective))
        solver.objective.constant = 0.0f;
    cons.marker = cons.other = am_Symbol();
}

int am_add_with_artificial(am_Solver *solver, am_Row *row, am_Constraint *cons) {
    am_Symbol a = am_newsymbol(solver, AM_SLACK);
    am_Term *term = null;
    am_Row tmp;
    int ret;
    --solver.symbol_count; /* artificial variable will be removed */
    am_initrow(&tmp);
    am_addrow(solver, &tmp, row, 1.0f);
    am_putrow(solver, a, row);
    am_initrow(row), row = null; /* row is useless */
    am_optimize(solver, &tmp);
    ret = am_nearzero(tmp.constant) ? AM_OK : AM_UNBOUND;
    am_freerow(solver, &tmp);
    if (am_getrow(solver, a, &tmp) == AM_OK) {
        am_Symbol entry = am_Symbol();
        if (am_isconstant(&tmp)) { am_freerow(solver, &tmp); return ret; }
        while (am_nextentry(&tmp.terms, cast(am_Entry**)&term))
            if (am_ispivotable(am_key(term))) { entry = am_key(term); break; }
        if (entry.id == 0) { am_freerow(solver, &tmp); return AM_UNBOUND; }
        am_solvefor(solver, &tmp, entry, a);
        am_substitute_rows(solver, entry, &tmp);
        am_putrow(solver, entry, &tmp);
    }
    while (am_nextentry(&solver.rows, cast(am_Entry**)&row)) {
        term = cast(am_Term*)am_gettable(&row.terms, a);
        if (term) am_delkey(&row.terms, &term.entry);
    }
    term = cast(am_Term*)am_gettable(&solver.objective.terms, a);
    if (term) am_delkey(&solver.objective.terms, &term.entry);
    if (ret != AM_OK) am_remove(cons);
    return ret;
}

int am_try_addrow(am_Solver *solver, am_Row *row, am_Constraint *cons) {
    am_Symbol subject = am_Symbol();
    am_Term *term = null;
    while (am_nextentry(&row.terms, cast(am_Entry**)&term))
        if (am_isexternal(am_key(term))) { subject = am_key(term); break; }
    if (subject.id == 0 && am_ispivotable(cons.marker)) {
        am_Term *mterm = cast(am_Term*)am_gettable(&row.terms, cons.marker);
        if (mterm.multiplier < 0.0f) subject = cons.marker;
    }
    if (subject.id == 0 && am_ispivotable(cons.other)) {
        am_Term *mterm = cast(am_Term*)am_gettable(&row.terms, cons.other);
        if (mterm.multiplier < 0.0f) subject = cons.other;
    }
    if (subject.id == 0) {
        while (am_nextentry(&row.terms, cast(am_Entry**)&term))
            if (!am_isdummy(am_key(term))) break;
        if (term is null) {
            if (am_nearzero(row.constant))
                subject = cons.marker;
            else {
                am_freerow(solver, row);
                return AM_UNSATISFIED;
            }
        }
    }
    if (subject.id == 0)
        return am_add_with_artificial(solver, row, cons);
    am_solvefor(solver, row, subject, am_Symbol());
    am_substitute_rows(solver, subject, row);
    am_putrow(solver, subject, row);
    return AM_OK;
}

am_Symbol am_get_leaving_row(am_Solver *solver, am_Symbol marker) {
    am_Symbol first = am_Symbol(), second = am_Symbol(), third = am_Symbol();
    am_Float r1 = am_Float.max, r2 = am_Float.max;
    am_Row *row = null;
    while (am_nextentry(&solver.rows, cast(am_Entry**)&row)) {
        am_Term *term = cast(am_Term*)am_gettable(&row.terms, marker);
        if (term is null) continue;
        if (am_isexternal(am_key(row))) third = am_key(row);
        else if (term.multiplier < 0.0f) {
            am_Float r = -row.constant / term.multiplier;
            if (r < r1) r1 = r, first = am_key(row);
        }
        else {
            am_Float r = row.constant / term.multiplier;
            if (r < r2) r2 = r, second = am_key(row);
        }
    }
    return first.id ? first : second.id ? second : third;
}

void am_delta_edit_constant(am_Solver *solver, am_Float delta, am_Constraint *cons) {
    am_Row *row;
    if ((row = cast(am_Row*)am_gettable(&solver.rows, cons.marker)) !is null)
    { if ((row.constant -= delta) < 0.0f) am_infeasible(solver, row); return; }
    if ((row = cast(am_Row*)am_gettable(&solver.rows, cons.other)) !is null)
    { if ((row.constant += delta) < 0.0f) am_infeasible(solver, row); return; }
    while (am_nextentry(&solver.rows, cast(am_Entry**)&row)) {
        am_Term *term = cast(am_Term*)am_gettable(&row.terms, cons.marker);
        if (term is null) continue;
        row.constant += term.multiplier*delta;
        if (am_isexternal(am_key(row)))
            am_markdirty(solver, am_sym2var(solver, am_key(row)));
        else if (row.constant < 0.0f)
            am_infeasible(solver, row);
    }
}

void am_dual_optimize(am_Solver *solver) {
    while (solver.infeasible_rows.id != 0) {
        am_Row tmp = void;
		am_Row *row =
            cast(am_Row*)am_gettable(&solver.rows, solver.infeasible_rows);
        am_Symbol enter = am_Symbol(), exit = am_key(row), curr;
        am_Term *objterm = void;
		am_Term *term = null;
        am_Float r, min_ratio = am_Float.max;
        solver.infeasible_rows = row.infeasible_next;
        row.infeasible_next = am_Symbol();
        if (row.constant >= 0.0f) continue;
        while (am_nextentry(&row.terms, cast(am_Entry**)&term)) {
            if (am_isdummy(curr = am_key(term)) || term.multiplier <= 0.0f)
                continue;
            objterm = cast(am_Term*)am_gettable(&solver.objective.terms, curr);
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

am_Solver *am_newsolver(am_Allocf allocf, void *ud) {
    am_Solver *solver;
    if (allocf is null) allocf = &am_default_allocf;
    if ((solver = cast(am_Solver*)allocf(ud, null, am_Solver.sizeof, 0)) is null)
        return null;
    memset(solver, 0, (*solver).sizeof);
    solver.allocf = allocf;
    solver.ud     = ud;
    am_initrow(&solver.objective);
    am_inittable(&solver.vars, am_VarEntry.sizeof);
    am_inittable(&solver.constraints, am_ConsEntry.sizeof);
    am_inittable(&solver.rows, am_Row.sizeof);
    solver.varpool  = am_MemPool(am_Variable.sizeof);
    solver.conspool = am_MemPool(am_Constraint.sizeof);
    return solver;
}

void am_delsolver(am_Solver *solver) {
    am_ConsEntry *ce = null;
    am_Row *row = null;
    while (am_nextentry(&solver.constraints, cast(am_Entry**)&ce))
        am_freerow(solver, &ce.constraint.expression);
    while (am_nextentry(&solver.rows, cast(am_Entry**)&row))
        am_freerow(solver, row);
    am_freerow(solver, &solver.objective);
    am_freetable(solver, &solver.vars);
    am_freetable(solver, &solver.constraints);
    am_freetable(solver, &solver.rows);
    am_freepool(solver, &solver.varpool);
    am_freepool(solver, &solver.conspool);
    solver.allocf(solver.ud, solver, 0, (*solver).sizeof);
}

void am_resetsolver(am_Solver *solver, int clear_constraints) {
    am_Entry *entry = null;
    if (!solver.auto_update) am_updatevars(solver);
    while (am_nextentry(&solver.vars, &entry)) {
        am_Constraint **cons = &(cast(am_VarEntry*)entry).variable.constraint;
        am_remove(*cons);
        *cons = null;
    }
    assert(am_nearzero(solver.objective.constant));
    assert(solver.infeasible_rows.id == 0);
    assert(solver.dirty_vars.id == 0);
    if (!clear_constraints) return;
    am_resetrow(&solver.objective);
    while (am_nextentry(&solver.constraints, &entry)) {
        am_Constraint *cons = (cast(am_ConsEntry*)entry).constraint;
        if (cons.marker.id == 0) continue;
        cons.marker = cons.other = am_Symbol();
    }
    while (am_nextentry(&solver.rows, &entry)) {
        am_delkey(&solver.rows, entry);
        am_freerow(solver, cast(am_Row*)entry);
    }
}

void am_updatevars(am_Solver *solver) {
    while (solver.dirty_vars.id != 0) {
        am_Variable *var = am_sym2var(solver, solver.dirty_vars);
        am_Row *row = cast(am_Row*)am_gettable(&solver.rows, var.sym);
        solver.dirty_vars = var.dirty_next;
        var.dirty_next = am_Symbol();
        var.value = row ? row.constant : 0.0f;
    }
}

int am_add(am_Constraint *cons) {
    am_Solver *solver = cons ? cons.solver : null;
    int ret, oldsym = solver ? solver.symbol_count : 0;
    am_Row row;
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

void am_remove(am_Constraint *cons) @nogc nothrow
{
    am_Solver *solver;
    am_Symbol marker;
    am_Row tmp;
    if (cons is null || cons.marker.id == 0) return;
    solver = cons.solver, marker = cons.marker;
    am_remove_errors(solver, cons);
    if (am_getrow(solver, marker, &tmp) != AM_OK) {
        am_Symbol exit = am_get_leaving_row(solver, marker);
        assert(exit.id != 0);
        am_getrow(solver, exit, &tmp);
        am_solvefor(solver, &tmp, marker, exit);
        am_substitute_rows(solver, marker, &tmp);
    }
    am_freerow(solver, &tmp);
    am_optimize(solver, &solver.objective);
    if (solver.auto_update) am_updatevars(solver);
}

int am_setstrength(am_Constraint *cons, am_Float strength)
{
    if (cons is null) return AM_FAILED;
    strength = am_nearzero(strength) ? AM_REQUIRED : strength;
    if (cons.strength == strength) return AM_OK;
    if (cons.strength >= AM_REQUIRED || strength >= AM_REQUIRED)
    { am_remove(cons), cons.strength = strength; return am_add(cons); }
    if (cons.marker.id != 0) {
        am_Solver *solver = cons.solver;
        am_Float diff = strength - cons.strength;
        am_mergerow(solver, &solver.objective, cons.marker, diff);
        am_mergerow(solver, &solver.objective, cons.other,  diff);
        am_optimize(solver, &solver.objective);
        if (solver.auto_update) am_updatevars(solver);
    }
    cons.strength = strength;
    return AM_OK;
}

int am_addedit(am_Variable *var, am_Float strength) {
    am_Solver *solver = var ? var.solver : null;
    am_Constraint *cons;
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

void am_deledit(am_Variable *var) {
    if (var is null || var.constraint is null) return;
    am_delconstraint(var.constraint);
    var.constraint = null;
    var.edit_value = 0.0f;
}

void am_suggest(am_Variable *var, am_Float value) {
    am_Solver *solver = var ? var.solver : null;
    am_Float delta;
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

