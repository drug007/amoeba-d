import core.stdc.stdarg;
import core.stdc.stdlib : free, realloc, malloc;
import core.stdc.stdio : printf, perror;

import cassowary.amoeba;

static size_t allmem = 0;
static size_t maxmem = 0;
static void *END = null;

void *debug_allocf(void *ud, void *ptr, size_t ns, size_t os) nothrow @nogc
{
	void *newptr = null;
	cast(void)ud;
	allmem += ns;
	allmem -= os;
	if (maxmem < allmem) maxmem = allmem;
	if (ns == 0) free(ptr);
	else newptr = realloc(ptr, ns);
version(DEBUG_MEMORY)
	printf("new(%p):\t+%d, old(%p):\t-%d\n", newptr, cast(int)ns, ptr, cast(int)os);
else
	return newptr;
}

void *null_allocf(void *ud, void *ptr, size_t ns, size_t os) nothrow @nogc
{ cast(void)ud, cast(void)ptr, cast(void)ns, cast(void)os; return null; }

void dumpkey(Symbol sym) {
	int ch = 'v';
	switch (sym.type) {
	case AM_EXTERNAL: ch = 'v'; break;
	case AM_SLACK:    ch = 's'; break;
	case AM_ERROR:    ch = 'e'; break;
	case AM_DUMMY:    ch = 'd'; break;
	default:
	}
	printf("%c%d", ch, cast(int)sym.id);
}

void dumprow(Row *row) {
	Term *term = null;
	printf("%g", row.constant);
	while (nextEntry(&row.terms, cast(Entry**)&term)) {
		Float multiplier = term.multiplier;
		printf(" %c ", multiplier > 0.0 ? '+' : '-');
		if (multiplier < 0.0) multiplier = -multiplier;
		if (!approx(multiplier, 1.0f))
			printf("%g*", multiplier);
		dumpkey(key(term));
	}
	printf("\n");
}

void dumpsolver(Solver *solver) {
	Row *row = null;
	int idx = 0;
	printf("-------------------------------\n");
	printf("solver: ");
	dumprow(&solver.objective);
	printf("rows(%d):\n", cast(int)solver.rows.count);
	while (nextEntry(&solver.rows, cast(Entry**)&row)) {
		printf("%d. ", ++idx);
		dumpkey(key(row));
		printf(" = ");
		dumprow(row);
	}
	printf("-------------------------------\n");
}

extern(C)
Constraint* new_constraint(Solver* in_solver, double in_strength,
		Variable* in_term1, double in_factor1, int in_relation,
		double in_constant, ...)
{
	int result;
	va_list argp;
	Constraint* c;
	assert(in_solver && in_term1);
	c = newConstraint(in_solver, cast(Float)in_strength);
	if(!c) return null;
	addTerm(c, in_term1, cast(Float)in_factor1);
	setRelation(c, in_relation);
	if(in_constant) addConstant(c, cast(Float)in_constant);
	va_start(argp, in_constant);
	while(1) {
		Variable* va_term = va_arg!(Variable*)(argp);
		double va_factor = va_arg!double(argp);
		if(va_term is null) break;
		addTerm(c, va_term, cast(Float)va_factor);
	}
	va_end(argp);
	result = add(c);
	assert(result == AM_OK);
	return c;
}

void test_all() {
	Solver *solver;
	Variable *xl;
	Variable *xm;
	Variable *xr;
	Variable *xd;
	Constraint* c1, c2, c3, c4, c5, c6;
	printf("\n\n==========\ntest all\n");

	solver = newSolver(&null_allocf, null);
	assert(solver is null);

	solver = newSolver(null, null);
	assert(solver !is null);
	delSolver(solver);

	solver = newSolver(&debug_allocf, null);
	xl = newVariable(solver);
	xm = newVariable(solver);
	xr = newVariable(solver);

	assert(xl.id == 1);
	assert(xm.id == 2);
	assert(xr.id == 3);
	assert(!hasEdit(null));
	assert(!hasEdit(xl));
	assert(!hasEdit(xm));
	assert(!hasEdit(xr));
	assert(!hasConstraint(null));

	xd = newVariable(solver);
	delVariable(xd);

	assert(setRelation(null, AM_GREATEQUAL) == AM_FAILED);

	c1 = newConstraint(solver, AM_REQUIRED);
	addTerm(c1, xl, 1.0);
	setRelation(c1, AM_GREATEQUAL);
	auto ret = add(c1);
	assert(ret == AM_OK);
	dumpsolver(solver);

	assert(setRelation(c1, AM_GREATEQUAL) == AM_FAILED);
	assert(setStrength(c1, AM_REQUIRED-10) == AM_OK);
	assert(setStrength(c1, AM_REQUIRED) == AM_OK);

	assert(hasConstraint(c1));
	assert(!hasEdit(xl));

	c2 = newConstraint(solver, AM_REQUIRED);
	addTerm(c2, xl, 1.0);
	setRelation(c2, AM_EQUAL);
	ret = add(c2);
	assert(ret == AM_OK);
	dumpsolver(solver);

	resetSolver(solver, 1);
	delConstraint(c1);
	delConstraint(c2);
	dumpsolver(solver);

	/* c1: 2*xm == xl + xr */
	c1 = newConstraint(solver, AM_REQUIRED);
	addTerm(c1, xm, 2.0);
	setRelation(c1, AM_EQUAL);
	addTerm(c1, xl, 1.0);
	addTerm(c1, xr, 1.0);
	ret = add(c1);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* c2: xl + 10 <= xr */
	c2 = newConstraint(solver, AM_REQUIRED);
	addTerm(c2, xl, 1.0);
	addConstant(c2, 10.0);
	setRelation(c2, AM_LESSEQUAL);
	addTerm(c2, xr, 1.0);
	ret = add(c2);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* c3: xr <= 100 */
	c3 = newConstraint(solver, AM_REQUIRED);
	addTerm(c3, xr, 1.0);
	setRelation(c3, AM_LESSEQUAL);
	addConstant(c3, 100.0);
	ret = add(c3);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* c4: xl >= 0 */
	c4 = newConstraint(solver, AM_REQUIRED);
	addTerm(c4, xl, 1.0);
	setRelation(c4, AM_GREATEQUAL);
	addConstant(c4, 0.0);
	ret = add(c4);
	assert(ret == AM_OK);
	dumpsolver(solver);

	c5 = cloneConstraint(c4, AM_REQUIRED);
	ret = add(c5);
	assert(ret == AM_OK);
	dumpsolver(solver);
	remove(c5);

	c5 = newConstraint(solver, AM_REQUIRED);
	addTerm(c5, xl, 1.0);
	setRelation(c5, AM_EQUAL);
	addConstant(c5, 0.0);
	ret = add(c5);
	assert(ret == AM_OK);

	c6 = cloneConstraint(c4, AM_REQUIRED);
	ret = add(c6);
	assert(ret == AM_OK);
	dumpsolver(solver);

	resetConstraint(c6);
	delConstraint(c6);

	remove(c1);
	remove(c2);
	remove(c3);
	remove(c4);
	dumpsolver(solver);
	ret |= add(c4);
	ret |= add(c3);
	ret |= add(c2);
	ret |= add(c1);
	assert(ret == AM_OK);

	resetSolver(solver, 0);
	resetSolver(solver, 1);
	printf("after reset\n");
	dumpsolver(solver);
	ret |= add(c1);
	ret |= add(c2);
	ret |= add(c3);
	ret |= add(c4);
	assert(ret == AM_OK);

	printf("after initialize\n");
	dumpsolver(solver);
	updateVars(solver);
	printf("xl: %f, xm: %f, xr: %f\n",
			xl.value,
			xm.value,
			xr.value);

	addEdit(xm, AM_MEDIUM);
	dumpsolver(solver);
	updateVars(solver);
	printf("xl: %f, xm: %f, xr: %f\n",
			xl.value,
			xm.value,
			xr.value);

	assert(hasEdit(xm));

	printf("suggest to 0.0\n");
	suggest(xm, 0.0);
	dumpsolver(solver);
	updateVars(solver);
	printf("xl: %f, xm: %f, xr: %f\n",
			xl.value,
			xm.value,
			xr.value);

	printf("suggest to 70.0\n");
	suggest(xm, 70.0);
	updateVars(solver);
	dumpsolver(solver);

	printf("xl: %f, xm: %f, xr: %f\n",
			xl.value,
			xm.value,
			xr.value);

	delEdit(xm);
	updateVars(solver);
	dumpsolver(solver);

	printf("xl: %f, xm: %f, xr: %f\n",
			xl.value,
			xm.value,
			xr.value);

	delSolver(solver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_binarytree()
{
	const int NUM_ROWS = 2;
	const int POINT_COUNT = 2^^NUM_ROWS - 1;
	const int X_OFFSET = 0;
	int nPointsCount, nResult;
	int nCurrentRowPointsCount = 1;
	int nCurrentRowFirstPointIndex = 0;
	Constraint *pC;
	Solver *pSolver;
	Variable*[POINT_COUNT] arrX, arrY;

	printf("\n\n==========\ntest binarytree\n");

	/* Create set of rules to distribute vertexes of a binary tree like this one:
	*      0
	*     / \
	*    /   \
	*   1     2
	*  / \   / \
	* 3   4 5   6
	*/

	pSolver = newSolver(&debug_allocf, null);

	/* Xroot=500, Yroot=10 */
	arrX[0] = newVariable(pSolver);
	arrY[0] = newVariable(pSolver);
	addEdit(arrX[0], AM_STRONG);
	addEdit(arrY[0], AM_STRONG);
	suggest(arrX[0], 500.0f + X_OFFSET);
	suggest(arrY[0], 10.0f);

	foreach (nRow; 1..NUM_ROWS)
	{
		int nPreviousRowFirstPointIndex = nCurrentRowFirstPointIndex;
		int nParentPoint = 0;
		nCurrentRowFirstPointIndex += nCurrentRowPointsCount;
		nCurrentRowPointsCount *= 2;

		foreach (nPoint; 0..nCurrentRowPointsCount)
		{
			arrX[nCurrentRowFirstPointIndex + nPoint] = newVariable(pSolver);
			arrY[nCurrentRowFirstPointIndex + nPoint] = newVariable(pSolver);

			/* Ycur = Yprev_row + 15 */
			pC = newConstraint(pSolver, AM_REQUIRED);
			addTerm(pC, arrY[nCurrentRowFirstPointIndex + nPoint], 1.0);
			setRelation(pC, AM_EQUAL);
			addTerm(pC, arrY[nCurrentRowFirstPointIndex - 1], 1.0);
			addConstant(pC, 15.0);
			nResult = add(pC);
			assert(nResult == AM_OK);

			if (nPoint > 0)
			{
				/* Xcur >= XPrev + 5 */
				pC = newConstraint(pSolver, AM_REQUIRED);
				addTerm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 1.0);
				setRelation(pC, AM_GREATEQUAL);
				addTerm(pC, arrX[nCurrentRowFirstPointIndex + nPoint - 1], 1.0);
				addConstant(pC, 5.0);
				nResult = add(pC);
				assert(nResult == AM_OK);
			}
			else
			{
				/* Xcur >= 0 */
				/* Comment from original C version: "When these lines added it crashes at the line 109" */
				pC = newConstraint(pSolver, AM_REQUIRED);
				addTerm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 1.0);
				setRelation(pC, AM_GREATEQUAL);
				addConstant(pC, 0.0);
				nResult = add(pC);
				assert(nResult == AM_OK);
			}

			if ((nPoint % 2) == 1)
			{
				/* Xparent = 0.5 * Xcur + 0.5 * Xprev */
				pC = newConstraint(pSolver, AM_REQUIRED);
				addTerm(pC, arrX[nPreviousRowFirstPointIndex + nParentPoint], 1.0);
				setRelation(pC, AM_EQUAL);
				addTerm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 0.5);
				addTerm(pC, arrX[nCurrentRowFirstPointIndex + nPoint - 1], 0.5);
				/* Comment from original C version: "It crashes here (at the 3rd call of add(...))!" */
				nResult = add(pC);
				assert(nResult == AM_OK);

				nParentPoint++;
			}
		}
	}
	nPointsCount = nCurrentRowFirstPointIndex + nCurrentRowPointsCount;
	pSolver.updateVars;
	dumpsolver(pSolver);

	{
		int i;
		for (i = 0; i < nPointsCount; i++)
			printf("Point %d: (%f, %f)\n", i,
					arrX[i].value, arrY[i].value);
	}

	delSolver(pSolver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_unbounded() {
	Solver *solver;
	Variable* x, y;
	Constraint *c;
	printf("\n\n==========\ntest unbound\n");

	solver = newSolver(&debug_allocf, null);
	x = newVariable(solver);
	y = newVariable(solver);

	/* 10.0 == 0.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addConstant(c, 10.0);
	setRelation(c, AM_EQUAL);
	auto ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNSATISFIED);
	dumpsolver(solver);

	/* 0.0 == 0.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addConstant(c, 0.0);
	setRelation(c, AM_EQUAL);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	resetSolver(solver, 1);

	/* x >= 10.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_GREATEQUAL);
	addConstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* x == 2*y */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_EQUAL);
	addTerm(c, y, 2.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* y == 3*x */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, y, 1.0);
	setRelation(c, AM_EQUAL);
	addTerm(c, x, 3.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNBOUND);
	dumpsolver(solver);

	resetSolver(solver, 1);

	/* x >= 10.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_GREATEQUAL);
	addConstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* x <= 0.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_LESSEQUAL);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNBOUND);
	dumpsolver(solver);

	printf("x: %f\n", x.value);

	resetSolver(solver, 1);

	/* x == 10.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_EQUAL);
	addConstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* x == 20.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_EQUAL);
	addConstant(c, 20.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNSATISFIED);
	dumpsolver(solver);

	/* x == 10.0 */
	c = newConstraint(solver, AM_REQUIRED);
	addTerm(c, x, 1.0);
	setRelation(c, AM_EQUAL);
	addConstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	delSolver(solver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_strength() {
	Solver *solver;
	Variable* x, y;
	Constraint *c;
	printf("\n\n==========\ntest strength\n");

	solver = newSolver(&debug_allocf, null);
	autoUpdate(solver, 1);
	x = newVariable(solver);
	y = newVariable(solver);

	/* x <= y */
	new_constraint(solver, AM_STRONG, x, 1.0, AM_LESSEQUAL, 0.0,
			y, 1.0, END);
	new_constraint(solver, AM_MEDIUM, x, 1.0, AM_EQUAL, 50, END);
	c = new_constraint(solver, AM_MEDIUM-10, y, 1.0, AM_EQUAL, 40, END);
	printf("%f, %f\n", x.value, y.value);
	assert(x.value == 50);
	assert(y.value == 50);

	setStrength(c, AM_MEDIUM+10);
	printf("%f, %f\n", x.value, y.value);
	assert(x.value == 40);
	assert(y.value == 40);

	setStrength(c, AM_MEDIUM-10);
	printf("%f, %f\n", x.value, y.value);
	assert(x.value == 50);
	assert(y.value == 50);

	delSolver(solver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_suggest() {
	version(all)
	{
		/* This should be valid but fails the (enter.id != 0) assertion in dual_optimize() */
		Float strength1 = AM_REQUIRED;
		Float strength2 = AM_REQUIRED;
		Float width = 76;
	}
	else
	{
		/* This mostly works, but still insists on forcing left_child_l = 0 which it should not */
		Float strength1 = AM_STRONG;
		Float strength2 = AM_WEAK;
		Float width = 76;
	}
	Float delta = 0;
	Float pos;
	Solver *solver;
	Variable* splitter_l,     splitter_w,     splitter_r;
	Variable* left_child_l,   left_child_w,   left_child_r;
	Variable* splitter_bar_l, splitter_bar_w, splitter_bar_r;
	Variable* right_child_l,  right_child_w,  right_child_r;
	printf("\n\n==========\ntest suggest\n");

	solver = newSolver(&debug_allocf, null);
	splitter_l = newVariable(solver);
	splitter_w = newVariable(solver);
	splitter_r = newVariable(solver);
	left_child_l = newVariable(solver);
	left_child_w = newVariable(solver);
	left_child_r = newVariable(solver);
	splitter_bar_l = newVariable(solver);
	splitter_bar_w = newVariable(solver);
	splitter_bar_r = newVariable(solver);
	right_child_l = newVariable(solver);
	right_child_w = newVariable(solver);
	right_child_r = newVariable(solver);

	/* splitter_r = splitter_l + splitter_w */
	/* left_child_r = left_child_l + left_child_w */
	/* splitter_bar_r = splitter_bar_l + splitter_bar_w */
	/* right_child_r = right_child_l + right_child_w */
	new_constraint(solver, AM_REQUIRED, splitter_r, 1.0, AM_EQUAL, 0.0,
			splitter_l, 1.0, splitter_w, 1.0, END);
	new_constraint(solver, AM_REQUIRED, left_child_r, 1.0, AM_EQUAL, 0.0,
			left_child_l, 1.0, left_child_w, 1.0, END);
	new_constraint(solver, AM_REQUIRED, splitter_bar_r, 1.0, AM_EQUAL, 0.0,
			splitter_bar_l, 1.0, splitter_bar_w, 1.0, END);
	new_constraint(solver, AM_REQUIRED, right_child_r, 1.0, AM_EQUAL, 0.0,
			right_child_l, 1.0, right_child_w, 1.0, END);

	/* splitter_bar_w = 6 */
	/* splitter_bar_l >= splitter_l + delta */
	/* splitter_bar_r <= splitter_r - delta */
	/* left_child_r = splitter_bar_l */
	/* right_child_l = splitter_bar_r */
	new_constraint(solver, AM_REQUIRED, splitter_bar_w, 1.0, AM_EQUAL, 6.0, END);
	new_constraint(solver, AM_REQUIRED, splitter_bar_l, 1.0, AM_GREATEQUAL,
			delta, splitter_l, 1.0, END);
	new_constraint(solver, AM_REQUIRED, splitter_bar_r, 1.0, AM_LESSEQUAL,
			-delta, splitter_r, 1.0, END);
	new_constraint(solver, AM_REQUIRED, left_child_r, 1.0, AM_EQUAL, 0.0,
			splitter_bar_l, 1.0, END);
	new_constraint(solver, AM_REQUIRED, right_child_l, 1.0, AM_EQUAL, 0.0,
			splitter_bar_r, 1.0, END);

	/* right_child_r >= splitter_r + 1 */
	/* left_child_w = 256 */
	new_constraint(solver, strength1, right_child_r, 1.0, AM_GREATEQUAL, 1.0,
			splitter_r, 1.0, END);
	new_constraint(solver, strength2, left_child_w, 1.0, AM_EQUAL, 256.0, END);

	/* splitter_l = 0 */
	/* splitter_r = 76 */
	new_constraint(solver, AM_REQUIRED, splitter_l, 1.0, AM_EQUAL, 0.0, END);
	new_constraint(solver, AM_REQUIRED, splitter_r, 1.0, AM_EQUAL, width, END);

	printf("\n\n==========\ntest suggest\n");
	for(pos = -10; pos < 86; pos++) {
		suggest(splitter_bar_l, pos);
		printf("pos: %4g | ", pos);
		printf("splitter_l l=%2g, w=%2g, r=%2g | ", splitter_l.value,
				splitter_w.value, splitter_r.value);
		printf("left_child_l l=%2g, w=%2g, r=%2g | ", left_child_l.value,
				left_child_w.value, left_child_r.value);
		printf("splitter_bar_l l=%2g, w=%2g, r=%2g | ", splitter_bar_l.value,
				splitter_bar_w.value, splitter_bar_r.value);
		printf("right_child_l l=%2g, w=%2g, r=%2g | ", right_child_l.value,
				right_child_w.value, right_child_r.value);
		printf("\n");
	}

	delSolver(solver);
	printf("allmem = %ld\n", allmem);
	printf("maxmem = %ld\n", maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_cycling() {
	Solver * solver = newSolver(null, null);

	Variable * va = newVariable(solver);
	Variable * vb = newVariable(solver);
	Variable * vc = newVariable(solver);
	Variable * vd = newVariable(solver);

	addEdit(va, AM_STRONG);
	printf("after edit\n");
	dumpsolver(solver);

	/* vb == va */
	{
		Constraint * c = newConstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addTerm(c, vb, 1.0);
		ret |= setRelation(c, AM_EQUAL);
		ret |= addTerm(c, va, 1.0);
		ret |= add(c);
		assert(ret == AM_OK);
		dumpsolver(solver);
	}

	/* vb == vc */
	{
		Constraint * c = newConstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addTerm(c, vb, 1.0);
		ret |= setRelation(c, AM_EQUAL);
		ret |= addTerm(c, vc, 1.0);
		ret |= add(c);
		assert(ret == AM_OK);
		dumpsolver(solver);
	}

	/* vc == vd */
	{
		Constraint * c = newConstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addTerm(c, vc, 1.0);
		ret |= setRelation(c, AM_EQUAL);
		ret |= addTerm(c, vd, 1.0);
		ret |= add(c);
		assert(ret == AM_OK);
		dumpsolver(solver);
	}

	/* vd == va */
	{
		Constraint * c = newConstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addTerm(c, vd, 1.0);
		ret |= setRelation(c, AM_EQUAL);
		ret |= addTerm(c, va, 1.0);
		ret |= add(c);
		assert(ret == AM_OK); /* asserts here */
		dumpsolver(solver);
	}
}

extern(C)
int main()
{
	test_binarytree();
	test_unbounded();
	test_strength();
	test_suggest();
	test_cycling();
	test_all();
	return 0;
}
