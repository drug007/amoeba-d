import core.stdc.stdarg;
import core.stdc.stdlib : free, realloc, malloc;
import core.stdc.stdio : printf, perror;

import cassowary.amoeba;

static size_t allmem = 0;
static size_t maxmem = 0;
static void *END = null;

extern(C)
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

extern(C)
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
	while (nextentry(&row.terms, cast(Entry**)&term)) {
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
	while (nextentry(&solver.rows, cast(Entry**)&row)) {
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
	c = newconstraint(in_solver, cast(Float)in_strength);
	if(!c) return null;
	addterm(c, in_term1, cast(Float)in_factor1);
	setrelation(c, in_relation);
	if(in_constant) addconstant(c, cast(Float)in_constant);
	va_start(argp, in_constant);
	while(1) {
		Variable* va_term = va_arg!(Variable*)(argp);
		double va_factor = va_arg!double(argp);
		if(va_term is null) break;
		addterm(c, va_term, cast(Float)va_factor);
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

	solver = newsolver(&null_allocf, null);
	assert(solver is null);

	solver = newsolver(null, null);
	assert(solver !is null);
	delsolver(solver);

	solver = newsolver(&debug_allocf, null);
	xl = newvariable(solver);
	xm = newvariable(solver);
	xr = newvariable(solver);

	assert(variableid(null) == -1);
	assert(variableid(xl) == 1);
	assert(variableid(xm) == 2);
	assert(variableid(xr) == 3);
	assert(!hasedit(null));
	assert(!hasedit(xl));
	assert(!hasedit(xm));
	assert(!hasedit(xr));
	assert(!hasconstraint(null));

	xd = newvariable(solver);
	delvariable(xd);

	assert(setrelation(null, AM_GREATEQUAL) == AM_FAILED);

	c1 = newconstraint(solver, AM_REQUIRED);
	addterm(c1, xl, 1.0);
	setrelation(c1, AM_GREATEQUAL);
	auto ret = add(c1);
	assert(ret == AM_OK);
	dumpsolver(solver);

	assert(setrelation(c1, AM_GREATEQUAL) == AM_FAILED);
	assert(setstrength(c1, AM_REQUIRED-10) == AM_OK);
	assert(setstrength(c1, AM_REQUIRED) == AM_OK);

	assert(hasconstraint(c1));
	assert(!hasedit(xl));

	c2 = newconstraint(solver, AM_REQUIRED);
	addterm(c2, xl, 1.0);
	setrelation(c2, AM_EQUAL);
	ret = add(c2);
	assert(ret == AM_OK);
	dumpsolver(solver);

	resetsolver(solver, 1);
	delconstraint(c1);
	delconstraint(c2);
	dumpsolver(solver);

	/* c1: 2*xm == xl + xr */
	c1 = newconstraint(solver, AM_REQUIRED);
	addterm(c1, xm, 2.0);
	setrelation(c1, AM_EQUAL);
	addterm(c1, xl, 1.0);
	addterm(c1, xr, 1.0);
	ret = add(c1);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* c2: xl + 10 <= xr */
	c2 = newconstraint(solver, AM_REQUIRED);
	addterm(c2, xl, 1.0);
	addconstant(c2, 10.0);
	setrelation(c2, AM_LESSEQUAL);
	addterm(c2, xr, 1.0);
	ret = add(c2);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* c3: xr <= 100 */
	c3 = newconstraint(solver, AM_REQUIRED);
	addterm(c3, xr, 1.0);
	setrelation(c3, AM_LESSEQUAL);
	addconstant(c3, 100.0);
	ret = add(c3);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* c4: xl >= 0 */
	c4 = newconstraint(solver, AM_REQUIRED);
	addterm(c4, xl, 1.0);
	setrelation(c4, AM_GREATEQUAL);
	addconstant(c4, 0.0);
	ret = add(c4);
	assert(ret == AM_OK);
	dumpsolver(solver);

	c5 = cloneconstraint(c4, AM_REQUIRED);
	ret = add(c5);
	assert(ret == AM_OK);
	dumpsolver(solver);
	remove(c5);

	c5 = newconstraint(solver, AM_REQUIRED);
	addterm(c5, xl, 1.0);
	setrelation(c5, AM_EQUAL);
	addconstant(c5, 0.0);
	ret = add(c5);
	assert(ret == AM_OK);

	c6 = cloneconstraint(c4, AM_REQUIRED);
	ret = add(c6);
	assert(ret == AM_OK);
	dumpsolver(solver);

	resetconstraint(c6);
	delconstraint(c6);

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

	resetsolver(solver, 0);
	resetsolver(solver, 1);
	printf("after reset\n");
	dumpsolver(solver);
	ret |= add(c1);
	ret |= add(c2);
	ret |= add(c3);
	ret |= add(c4);
	assert(ret == AM_OK);

	printf("after initialize\n");
	dumpsolver(solver);
	updatevars(solver);
	printf("xl: %f, xm: %f, xr: %f\n",
			value(xl),
			value(xm),
			value(xr));

	addedit(xm, AM_MEDIUM);
	dumpsolver(solver);
	updatevars(solver);
	printf("xl: %f, xm: %f, xr: %f\n",
			value(xl),
			value(xm),
			value(xr));

	assert(hasedit(xm));

	printf("suggest to 0.0\n");
	suggest(xm, 0.0);
	dumpsolver(solver);
	updatevars(solver);
	printf("xl: %f, xm: %f, xr: %f\n",
			value(xl),
			value(xm),
			value(xr));

	printf("suggest to 70.0\n");
	suggest(xm, 70.0);
	updatevars(solver);
	dumpsolver(solver);

	printf("xl: %f, xm: %f, xr: %f\n",
			value(xl),
			value(xm),
			value(xr));

	deledit(xm);
	updatevars(solver);
	dumpsolver(solver);

	printf("xl: %f, xm: %f, xr: %f\n",
			value(xl),
			value(xm),
			value(xr));

	delsolver(solver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_binarytree() {
	const int NUM_ROWS = 9;
	const int X_OFFSET = 0;
	int nPointsCount, nResult, nRow;
	int nCurrentRowPointsCount = 1;
	int nCurrentRowFirstPointIndex = 0;
	Constraint *pC;
	Solver *pSolver;
	Variable** arrX, arrY;

	printf("\n\n==========\ntest binarytree\n");
	arrX = cast(Variable**)malloc(2048 * (Variable*).sizeof);
	if (arrX is null) return;
	arrY = arrX + 1024;

	/* Create set of rules to distribute vertexes of a binary tree like this one:
	*      0
	*     / \
	*    /   \
	*   1     2
	*  / \   / \
	* 3   4 5   6
	*/

	pSolver = newsolver(&debug_allocf, null);

	/* Xroot=500, Yroot=10 */
	arrX[0] = newvariable(pSolver);
	arrY[0] = newvariable(pSolver);
	addedit(arrX[0], AM_STRONG);
	addedit(arrY[0], AM_STRONG);
	suggest(arrX[0], 500.0f + X_OFFSET);
	suggest(arrY[0], 10.0f);

	for (nRow = 1; nRow < NUM_ROWS; nRow++) {
		int nPreviousRowFirstPointIndex = nCurrentRowFirstPointIndex;
		int nPoint, nParentPoint = 0;
		nCurrentRowFirstPointIndex += nCurrentRowPointsCount;
		nCurrentRowPointsCount *= 2;

		for (nPoint = 0; nPoint < nCurrentRowPointsCount; nPoint++) {
			arrX[nCurrentRowFirstPointIndex + nPoint] = newvariable(pSolver);
			arrY[nCurrentRowFirstPointIndex + nPoint] = newvariable(pSolver);

			/* Ycur = Yprev_row + 15 */
			pC = newconstraint(pSolver, AM_REQUIRED);
			addterm(pC, arrY[nCurrentRowFirstPointIndex + nPoint], 1.0);
			setrelation(pC, AM_EQUAL);
			addterm(pC, arrY[nCurrentRowFirstPointIndex - 1], 1.0);
			addconstant(pC, 15.0);
			nResult = add(pC);
			assert(nResult == AM_OK);

			if (nPoint > 0) {
				/* Xcur >= XPrev + 5 */
				pC = newconstraint(pSolver, AM_REQUIRED);
				addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 1.0);
				setrelation(pC, AM_GREATEQUAL);
				addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint - 1], 1.0);
				addconstant(pC, 5.0);
				nResult = add(pC);
				assert(nResult == AM_OK);
			} else {
				/* When these lines added it crashes at the line 109 */
				pC = newconstraint(pSolver, AM_REQUIRED);
				addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 1.0);
				setrelation(pC, AM_GREATEQUAL);
				addconstant(pC, 0.0);
				nResult = add(pC);
				assert(nResult == AM_OK);
			}

			if ((nPoint % 2) == 1) {
				/* Xparent = 0.5 * Xcur + 0.5 * Xprev */
				pC = newconstraint(pSolver, AM_REQUIRED);
				addterm(pC, arrX[nPreviousRowFirstPointIndex + nParentPoint], 1.0);
				setrelation(pC, AM_EQUAL);
				addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint], 0.5);
				addterm(pC, arrX[nCurrentRowFirstPointIndex + nPoint - 1], 0.5);
				/* It crashes here (at the 3rd call of add(...))!  */
				nResult = add(pC);
				assert(nResult == AM_OK);

				nParentPoint++;
			}
		}
	}
	nPointsCount = nCurrentRowFirstPointIndex + nCurrentRowPointsCount;

	/*{
		int i;
		for (i = 0; i < nPointsCount; i++)
			printf("Point %d: (%f, %f)\n", i,
					value(arrX[i]), value(arrY[i]));
	}*/

	delsolver(pSolver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	free(arrX);
	maxmem = 0;
}

void test_unbounded() {
	Solver *solver;
	Variable* x, y;
	Constraint *c;
	printf("\n\n==========\ntest unbound\n");

	solver = newsolver(&debug_allocf, null);
	x = newvariable(solver);
	y = newvariable(solver);

	/* 10.0 == 0.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addconstant(c, 10.0);
	setrelation(c, AM_EQUAL);
	auto ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNSATISFIED);
	dumpsolver(solver);

	/* 0.0 == 0.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addconstant(c, 0.0);
	setrelation(c, AM_EQUAL);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	resetsolver(solver, 1);

	/* x >= 10.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_GREATEQUAL);
	addconstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* x == 2*y */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_EQUAL);
	addterm(c, y, 2.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* y == 3*x */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, y, 1.0);
	setrelation(c, AM_EQUAL);
	addterm(c, x, 3.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNBOUND);
	dumpsolver(solver);

	resetsolver(solver, 1);

	/* x >= 10.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_GREATEQUAL);
	addconstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* x <= 0.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_LESSEQUAL);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNBOUND);
	dumpsolver(solver);

	printf("x: %f\n", value(x));

	resetsolver(solver, 1);

	/* x == 10.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_EQUAL);
	addconstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	/* x == 20.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_EQUAL);
	addconstant(c, 20.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_UNSATISFIED);
	dumpsolver(solver);

	/* x == 10.0 */
	c = newconstraint(solver, AM_REQUIRED);
	addterm(c, x, 1.0);
	setrelation(c, AM_EQUAL);
	addconstant(c, 10.0);
	ret = add(c);
	printf("ret = %d\n", ret);
	assert(ret == AM_OK);
	dumpsolver(solver);

	delsolver(solver);
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

	solver = newsolver(&debug_allocf, null);
	autoupdate(solver, 1);
	x = newvariable(solver);
	y = newvariable(solver);

	/* x <= y */
	new_constraint(solver, AM_STRONG, x, 1.0, AM_LESSEQUAL, 0.0,
			y, 1.0, END);
	new_constraint(solver, AM_MEDIUM, x, 1.0, AM_EQUAL, 50, END);
	c = new_constraint(solver, AM_MEDIUM-10, y, 1.0, AM_EQUAL, 40, END);
	printf("%f, %f\n", value(x), value(y));
	assert(value(x) == 50);
	assert(value(y) == 50);

	setstrength(c, AM_MEDIUM+10);
	printf("%f, %f\n", value(x), value(y));
	assert(value(x) == 40);
	assert(value(y) == 40);

	setstrength(c, AM_MEDIUM-10);
	printf("%f, %f\n", value(x), value(y));
	assert(value(x) == 50);
	assert(value(y) == 50);

	delsolver(solver);
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

	solver = newsolver(&debug_allocf, null);
	splitter_l = newvariable(solver);
	splitter_w = newvariable(solver);
	splitter_r = newvariable(solver);
	left_child_l = newvariable(solver);
	left_child_w = newvariable(solver);
	left_child_r = newvariable(solver);
	splitter_bar_l = newvariable(solver);
	splitter_bar_w = newvariable(solver);
	splitter_bar_r = newvariable(solver);
	right_child_l = newvariable(solver);
	right_child_w = newvariable(solver);
	right_child_r = newvariable(solver);

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
		printf("splitter_l l=%2g, w=%2g, r=%2g | ", value(splitter_l),
				value(splitter_w), value(splitter_r));
		printf("left_child_l l=%2g, w=%2g, r=%2g | ", value(left_child_l),
				value(left_child_w), value(left_child_r));
		printf("splitter_bar_l l=%2g, w=%2g, r=%2g | ", value(splitter_bar_l),
				value(splitter_bar_w), value(splitter_bar_r));
		printf("right_child_l l=%2g, w=%2g, r=%2g | ", value(right_child_l),
				value(right_child_w), value(right_child_r));
		printf("\n");
	}

	delsolver(solver);
	printf("allmem = %d\n", cast(int)allmem);
	printf("maxmem = %d\n", cast(int)maxmem);
	assert(allmem == 0);
	maxmem = 0;
}

void test_cycling() {
	Solver * solver = newsolver(null, null);

	Variable * va = newvariable(solver);
	Variable * vb = newvariable(solver);
	Variable * vc = newvariable(solver);
	Variable * vd = newvariable(solver);

	addedit(va, AM_STRONG);
	printf("after edit\n");
	dumpsolver(solver);

	/* vb == va */
	{
		Constraint * c = newconstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addterm(c, vb, 1.0);
		ret |= setrelation(c, AM_EQUAL);
		ret |= addterm(c, va, 1.0);
		ret |= add(c);
		assert(ret == AM_OK);
		dumpsolver(solver);
	}

	/* vb == vc */
	{
		Constraint * c = newconstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addterm(c, vb, 1.0);
		ret |= setrelation(c, AM_EQUAL);
		ret |= addterm(c, vc, 1.0);
		ret |= add(c);
		assert(ret == AM_OK);
		dumpsolver(solver);
	}

	/* vc == vd */
	{
		Constraint * c = newconstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addterm(c, vc, 1.0);
		ret |= setrelation(c, AM_EQUAL);
		ret |= addterm(c, vd, 1.0);
		ret |= add(c);
		assert(ret == AM_OK);
		dumpsolver(solver);
	}

	/* vd == va */
	{
		Constraint * c = newconstraint(solver, AM_REQUIRED);
		int ret = 0;
		ret |= addterm(c, vd, 1.0);
		ret |= setrelation(c, AM_EQUAL);
		ret |= addterm(c, va, 1.0);
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
