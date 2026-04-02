r"""
To add handling of a FriCAS type constructor, proceed as follows:

* in ``LazyParent``, add the translation of the contructor to a
  SageMath parent.

* in ``fricas.spad``, add an appropriate package, if necessary.

* in ``dispatch_table``, map the type constructor to a function that
  constructs the package containing ``sexport`` and a function that
  constructs the element given the parsed string produced by
  ``sexport``.

"""
from sage.misc.cachefunc import cached_method
from sage.misc.lazy_import import lazy_import
from sage.rings.integer import Integer
lazy_import('sage.calculus.var', ['var', 'function'])
lazy_import('sage.symbolic.expression', ['symbol_table', 'register_symbol'])
lazy_import('sage.symbolic.constants', ['I', 'e', 'pi'])

FRICAS_CONSTANTS = {'%i': I,
                    '%e': e,
                    '%pi': pi}

# the dispatch dictionary for SEXPorter and Evaluator
_DISPATCH = {"Integer": ("_inputform", "_eval_simple"),
             "PositiveInteger": ("_inputform", "_eval_simple"),
             "Expression": ("_inputform", "_eval_sr"),
             "PrimeField": ("_finite", "_eval_gf"),
             "FiniteField": ("_finite", "_eval_gf"),
             "Fraction": ("_simple", "_eval_fraction"),
             "List": ("_simple", "_eval_list"),
             "Matrix": ("_simple", "_eval_matrix"),
             "Polynomial": ("_simple", "_eval_polynomialring"),
             "Factored": ("_simple", "_eval_factorization"),
             "DistributedMultivariatePolynomial": ("_list_symbol", "_eval_polynomialring")}

class SEXPorter:
    def __init__(self, domain):
        """
        INPUT:

        - ``domain`` -- a nested list of strings and integers,
          describing a FriCAS domain.
        """
        self._domain = domain

    def _unparse(self):
        """
        Return the FriCAS domain as a string.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import SEXPorter
            sage: SEXPorter(("Fraction", ("FiniteField", 2, 3)))._unparse()
            'Fraction(FiniteField(2,3))'
        """
        if not isinstance(self._domain, tuple):
            return str(self._domain)

        if len(self._domain) == 1:
            return str(self._domain[0])

        return (self._domain[0] + "("
                + ",".join(SEXPorter(e)._unparse() for e in self._domain[1:])
                + ")")

    def _inputform(self):
        return f"InputFormExport({self._unparse()})"

    def _finite(self):
        return f"FiniteExport({self._unparse()})"

    def _simple(self):
        inner = SEXPorter(self._domain[1])
        base_str = inner._unparse()
        export_str = inner.package_call()

        return f"SimpleExport({base_str}, {export_str})"

    def _list_symbol(self):
        args_str = "[" + ",".join(f'"{s}"' for s in self._domain[1]) + "]"
        inner = SEXPorter(self._domain[2])
        base_str = inner._unparse()
        export_str = inner.package_call()

        return f"ListSymbolExport({args_str}, {base_str}, {export_str})"

    def package_call(self):
        """
        Return the package containing the ``sexport`` function.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import SEXPorter
            sage: SEXPorter(("List", ("FiniteField", 2, 3))).package_call()
            'SimpleExport(FiniteField(2,3), FiniteExport(FiniteField(2,3)))'
        """
        if not isinstance(self._domain, tuple):
            return f"InputFormExport({self._domain})"
        head = self._domain[0]
        return getattr(self, _DISPATCH[head][0])()

class SEXEvaluator:
    def __init__(self, ast, dom):
        """
        INPUT:

        - ``ast`` -- a nested list of strings and integers describing a FriCAS object
        - ``dom`` -- a :cls:`LazyParent` describing the domain of ``ast``
        """
        self._ast = ast
        self._dom = dom

    def eval(self):
        r"""
        Return the evaluation of ``self`` in the given parent.
        """
        head = self._dom.head()
        return getattr(self, _DISPATCH[head][1])()

    # specific evaluators
    # the naming convention is the parent in sage, in lower case

    def _eval_simple(self):
        r"""
        Return the evaluation by passing it to the parent.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import LazyParent, SEXEvaluator
            sage: SEXEvaluator("-5", LazyParent(['Integer']))._eval_simple()
            -5
        """
        return self._dom.parent()(self._ast)

    def _eval_gf(self):
        r"""
        Return the evaluation as an element of a finite field.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import SEXEvaluator, LazyParent
            sage: SEXEvaluator(5, LazyParent(['FiniteField', 2, 3]))._eval_gf()
            z3^2 + 1
        """
        return self._dom.parent().from_integer(self._ast)

    def _eval_list(self):
        r"""
        Return the evaluation as a list.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import SEXParser, LazyParent, SEXEvaluator
            sage: ast = SEXParser("(1 2 3)", raw=True).parse()
            sage: dom = LazyParent(('List', ('Integer',)))
            sage: SEXEvaluator(ast, dom)._eval_list()
            [1, 2, 3]
        """
        base = self._dom.base()
        return [SEXEvaluator(a, base).eval() for a in self._ast]

    def _eval_fraction(self):
        r"""
        Return the evaluation as a fraction.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import SEXParser, LazyParent, SEXEvaluator
            sage: ast = SEXParser("(3 2)", raw=True).parse()
            sage: SEXEvaluator(ast, LazyParent(('Fraction', ('Integer',))))._eval_fraction()
            3/2
        """
        base = self._dom.base()
        if not isinstance(self._ast, tuple):
            num = SEXEvaluator(self._ast, base).eval()
            return dom.parent()(num)

        a, b = self._ast
        num = SEXEvaluator(a, base).eval()
        den = SEXEvaluator(b, base).eval()
        return num / den

    def _eval_matrix(self):
        r"""
        Return the evaluation of ``ast`` as a matrix.

        EXAMPLES::

            sage: from sage.interfaces.fricas_translator import SEXParser, LazyParent, SEXEvaluator
            sage: ast = SEXParser("((1 2) (3 4))", raw=True).parse()
            sage: SEXEvaluator(ast, LazyParent(('Matrix', ('Integer',))))._eval_matrix()
            [1 2]
            [3 4]
        """
        base = self._dom.base()
        m = [[SEXEvaluator(e, base).eval() for e in row]
             for row in self._ast]
        if not m:
            return self._dom.parent(nrows=0, ncols=0)(m)
        return self._dom.parent(nrows=len(m), ncols=len(m[0]))(m)

    def _eval_polynomialring(self):
        r"""
        Return the evaluation as a polynomial.

        EXAMPLES::

            sage: fricas('(3 + x/2 + 5*y*x)::DMP(["x", "y", "z"], FRAC INT)').sage()
        """
        raise NotImplementedError


    def _eval_sr_aux(self):
        r"""
        Return the evaluation as an element of the
        symbolic ring.

        Post processing by :meth:`_eval_sr` is necessary.

        EXAMPLES:

        This function cannot use the symbol table to translate
        symbols which are not function calls, as :issue:`31849` shows
        ``D`` would erroneously be interpreted as differential
        then::

            sage: var("D")
            D
            sage: integrate(D/x, x, algorithm='fricas')
            D*log(x)

        However, it does have to check for constants, for example
        ``%pi``::

            sage: from sage.interfaces.fricas_translator import SEXEvaluator
            sage: SEXEvaluator("%pi", None)._eval_sr_aux()
            pi
        """
        from sage.symbolic.ring import SR

        if isinstance(self._ast, (Integer, float)):
            return SR(self._ast)

        if isinstance(self._ast, str):
            try:
                return FRICAS_CONSTANTS[self._ast]
            except KeyError:
                return var(self._ast.replace("%", "_"))

        f, args = self._ast
        args_eval = [SEXEvaluator(a, self._dom)._eval_sr_aux() for a in args]

        try:
            fun = symbol_table["fricas"][(f, len(args_eval))]
        except KeyError:
            try:
                fun = symbol_table["fricas"][(f, -1)]
            except KeyError:
                fun = function(f)

        return fun(*args_eval)

    def _eval_sr(self):
        r"""
        Evaluate as element of the symbolic ring.

        TESTS::

            sage: f = fricas('integrate(sin(x^2), x)'); f
                       +---+
                       | 2
            fresnelS(x |--- )
                      \|%pi
            -----------------
                   +---+
                   | 2
                   |---
                  \|%pi
            sage: f.sage()
            1/2*sqrt(2)*sqrt(pi)*fresnel_sin(sqrt(2)*x/sqrt(pi))

        Check that :issue:`22525` is fixed::

            sage: l = [sin, cos, sec, csc, cot, tan, asin, acos, atan, acot, acsc, asec, arcsin, arccos, arctan, arccot, arccsc, arcsec]
            sage: [f(x)._fricas_().sage().subs(x=0.9) for f in l]
            [0.783326909627483,
             0.621609968270664,
             1.60872581046605,
             1.27660621345890,
             0.793551147842317,
             1.26015821755034,
             1.11976951499863,
             0.451026811796262,
             0.732815101786507,
             0.837981225008390,
             1.57079632679490 - 0.467145308103262*I,
             0.467145308103262*I,
             1.11976951499863,
             0.451026811796262,
             0.732815101786507,
             0.837981225008390,
             1.57079632679490 - 0.467145308103262*I,
             0.467145308103262*I]
            sage: l = [tanh, sinh, cosh, coth, sech, csch, asinh, acosh, atanh, acoth, asech, acsch, arcsinh, arccosh, arctanh, arccoth, arcsech, arccsch]
            sage: [f(x)._fricas_().sage().subs(x=0.9) for f in l]
            [0.716297870199024,
             1.02651672570818,
             1.43308638544877,
             1.39606725303001,
             0.697794641100332,
             0.974168247780004,
             0.808866935652782,
             0.451026811796262*I,
             1.47221948958322,
             1.47221948958322 - 1.57079632679490*I,
             0.467145308103262,
             0.957800449200672,
             0.808866935652782,
             0.451026811796262*I,
             1.47221948958322,
             1.47221948958322 - 1.57079632679490*I,
             0.467145308103262,
             0.957800449200672]

        Check that :issue:`23782` is fixed::

            sage: s = '((3*n^10-25*n^9+50*n^8+62*n^7-229*n^6-25*n^5+320*n^4-12*n^3-144*n^2)/11520)::EXPR INT'
            sage: fricas(s).sage()
            1/3840*n^10 - 5/2304*n^9 + 5/1152*n^8 + 31/5760*n^7 - 229/11520*n^6 - 5/2304*n^5 + 1/36*n^4 - 1/960*n^3 - 1/80*n^2

        Some checks for digamma and polygamma (:issue:`31853`)::

            sage: fricas.digamma(1.0)
            - 0.5772156649_0153286061
            sage: psi(1.0)
            -0.577215664901533
            sage: fricas.polygamma(1, 1.0)
            1.644934066848226...
            sage: psi(1, 1).n()
            1.64493406684823

            sage: var("w")
            w
            sage: fricas.laplace(log(x), x, w).sage()
            -(euler_gamma + log(w))/w

        Check that :issue:`25224` is fixed::

            sage: integrate(log(x)/(1-x),x,algorithm='fricas')
            dilog(-x + 1)
            sage: fricas(dilog(-x + 1))
            dilog(x)
            sage: dilog._fricas_()(1.0)
            1.6449340668_4822643647_24152
            sage: dilog(1.0)
            1.64493406684823

        Check that :issue:`25987` is fixed::

            sage: integrate(lambert_w(x), x, algorithm='fricas')
            (x*lambert_w(x)^2 - x*lambert_w(x) + x)/lambert_w(x)

        Check that :issue:`25838` is fixed::

            sage: F = function('f'); f = SR.var('f')
            sage: FF = fricas(F(f)); FF
            f(f)
            sage: FF.D(f).sage()
            diff(f(f), f)
            sage: bool(FF.D(f).integrate(f).sage() == F(f))
            True

        Check that :issue:`25602` is fixed::

            sage: r = fricas.integrate(72000/(1+x^5), x).sage()
            sage: abs(n(r.subs(x=5) - r.subs(x=3)) - 193.020947266210) <= 0.1
            True

            sage: var("a"); r = fricas.integrate(72000*a^8/(a^5+x^5), x).sage()
            a
            sage: abs(n(r.subs(a=1, x=5) - r.subs(a=1, x=3)) - 193.020947266268) <= 0.1
            True

        Check conversions of sums and products::

            sage: var("k, m, n")
            (k, m, n)
            sage: fricas("sum(1/factorial(k), k=1..n)").sage()
            sum(1/factorial(_...), _..., 1, n)
            sage: fricas("eval(sum(x/k, k=1..n), x=k)").sage()
            k*harmonic_number(n)
            sage: fricas("product(1/factorial(k), k=1..n)").sage()
            1/product(factorial(_...), _..., 1, n)

            sage: f = fricas.guess([sum(1/k, k,1,n) for n in range(10)])[0]; f
             n - 1
              --+       1
              >      -------
              --+    s   + 1
            s   = 0   10
             10

            sage: f.sage()
            harmonic_number(n)

            sage: f = fricas.guess([0, 1, 3, 9, 33])[0]; f
                    s  - 1
            n - 1    5
             --+    ++-++
             >       | |    p  + 2
             --+     | |     4
            s  = 0  p  = 0
             5       4

            sage: f.sage()
            sum(factorial(_... + 1), _..., 0, n - 1)

        Check that :issue:`26746` is fixed::

            sage: _ = var('x, y, z')
            sage: f = sin(x^2) + y^z
            sage: f.integrate(x, algorithm='fricas')
            1/2*sqrt(2)*sqrt(pi)*(sqrt(2)*x*y^z/sqrt(pi) + fresnel_sin(sqrt(2)*x/sqrt(pi)))

            sage: fricas(fresnel_sin(1))
            fresnelS(1)
            sage: fricas("fresnelS(1.0)")
            0.4382591473_9035476607_676

            sage: fricas(fresnel_cos(1))
            fresnelC(1)
            sage: fricas("fresnelC(1.0)")
            0.7798934003_7682282947_42

        Check that :issue:`17908` is fixed::

            sage: fricas(abs(x)).sage().subs(x=-1783)
            1783

        Check that :issue:`27310` is fixed::

            sage: fricas.set("F", "operator 'f")
            sage: fricas("eval(D(F(x,y), [x, y], [2, 1]), x=x+y)").sage()
            D[0, 0, 1](f)(x + y, y)

        Conversion of hypergeometric functions (:issue:`31298`)::

            sage: a,b,c = var("a b c")
            sage: A = hypergeometric([a, b], [c], x)
            sage: fricas(A).sage() - A
            0
            sage: fricas(A).D(x).sage() - diff(A, x)
            0

        Check that :issue:`31858` is fixed::

            sage: fricas.Gamma(3/2).sage()
            1/2*sqrt(pi)
            sage: fricas.Gamma(3/4).sage()
            gamma(3/4)
            sage: fricas.Gamma(3, 2).sage()
            gamma(3, 2)


        Check that :issue:`32133` is fixed::

            sage: var("y")
            y
            sage: f = fricas.zerosOf(y^4 + y + 1, y); f
                        +-----------------------------+
                        |       2                    2
                       \|- 3 %y1  - 2 %y0 %y1 - 3 %y0   - %y1 - %y0
            [%y0, %y1, --------------------------------------------,
                                             2
                +-----------------------------+
                |       2                    2
             - \|- 3 %y1  - 2 %y0 %y1 - 3 %y0   - %y1 - %y0
             ----------------------------------------------]
                                    2

            sage: f[1].sage()
            -1/2*sqrt(1/3)*sqrt((3*(1/18*I*sqrt(229)*sqrt(3) + 1/2)^(2/3) + 4)/(1/18*I*sqrt(229)*sqrt(3) + 1/2)^(1/3)) + 1/2*sqrt(-(1/18*I*sqrt(229)*sqrt(3) + 1/2)^(1/3) + 6*sqrt(1/3)/sqrt((3*(1/18*I*sqrt(229)*sqrt(3) + 1/2)^(2/3) + 4)/(1/18*I*sqrt(229)*sqrt(3) + 1/2)^(1/3)) - 4/3/(1/18*I*sqrt(229)*sqrt(3) + 1/2)^(1/3))
        """
        # a FriCAS expressions may contain implicit references to a
        # rootOf expression within itself, as for example in the
        # result of integrate(1/(1+x^5), x).  Each algebraic number
        # appearing in the expression is only introduced once and
        # assigned a variable (usually of the form %%...).
        rootOf = dict()  # (variable, polynomial)
        rootOf_ev = dict()  # variable -> (complex) algebraic number

        def convert_rootOf(x, y):
            if y in rootOf:
                assert rootOf[y] == x
            else:
                rootOf[y] = x
            return y

        register_symbol(convert_rootOf, {'fricas': 'rootOf'}, 2)
        ex = self._eval_sr_aux()

        # postprocessing of rootOf
        from sage.rings.qqbar import QQbar
        from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
        while rootOf:
            for var, poly in rootOf.items():
                pvars = poly.variables()
                rvars = [v for v in pvars if v not in rootOf_ev]  # remaining variables
                uvars = [v for v in rvars if v in rootOf]  # variables to evaluate
                if len(uvars) == 1:
                    assert uvars[0] == var, "the only variable in uvars should be %s but is %s" % (var, uvars[0])
                    break
            else:
                assert False, "circular dependency in rootOf expression"
            # substitute known roots
            poly = poly.subs(rootOf_ev)
            evars = set(poly.variables()).difference([var])
            del rootOf[var]
            if evars:
                # we just need any root per FriCAS specification -
                # however, if there are extra variables, we cannot
                # use QQbar.any_root
                rootOf_ev[var] = poly.roots(var, multiplicities=False)[0]
            else:
                R = PolynomialRing(QQbar, "x")
                # PolynomialRing does not accept variable names with
                # leading underscores
                poly = R(poly.subs({var: R.gen()}))
                # we just need any root per FriCAS specification
                rootOf_ev[var] = poly.any_root()

        return ex.subs({var: (val.radical_expression()
                              if val.parent() is QQbar else val)
                        for var, val in rootOf_ev.items()})

class LazyParent:
    def __init__(self, domain):
        self.domain = domain

    def head(self):
        return self.domain[0]

    def args(self):
        return self.domain[1:]

    @cached_method
    def base(self):
        head = self.head()
        args = self.args()
        if head in ["List", "Matrix", "Polynomial", "Fraction"]:
            return LazyParent(args[0])

        if head in ["DistributedMultivariatePolynomial"]:
            return LazyParent(args[1])

        raise NotImplementedError(f"Cannot build base for {head}")

    @cached_method
    def parent(self, **kwargs):
        head = self.head()
        args = self.args()

        if head == "FiniteField":
            from sage.rings.finite_rings.finite_field_constructor import GF
            p, e = args
            return GF(p, e)

        if head == "PrimeField":
            from sage.rings.finite_rings.finite_field_constructor import GF
            return GF(args[0])

        if head in ["Integer", "PositiveInteger"]:
            from sage.rings.integer_ring import ZZ
            return ZZ

        if head == "Fraction":
            from sage.rings.fraction_field import FractionField
            return FractionField(self.base().parent())

        if head in ["DistributedMultivariatePolynomial"]:
            from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
            return PolynomialRing(self.base().parent(), args[0])

        if head == "Matrix":
            from sage.matrix.matrix_space import MatrixSpace
            base = self.base().parent()
            nrows = kwargs["nrows"]
            ncols = kwargs["ncols"]
            return MatrixSpace(base, nrows, ncols)

        raise NotImplementedError(f"Cannot build parent for {head}")


class SEXParser:
    _WHITESPACE = " "
    _LEFTBRACKET = "("
    _RIGHTBRACKET = ")"
    _STRINGMARKER = '"'
    _ESCAPEMARKER = '_'  # STRINGMARKER must be escaped in strings

    def __init__(self, s, raw=False):
        """
        INPUT:

        - ``s`` -- string
        - ``raw`` -- boolean; whether the first element of a list
          should never be interpreted as a function call
        """
        self._raw = raw
        self._s = s
        self._start = 0  # specifies where to start parsing

    def parse(self):
        r"""
        Parse the string.

        TESTS::

            sage: from sage.interfaces.fricas_translator import SEXParser
            sage: SEXParser("abc").parse()
            'abc'

            sage: SEXParser("(asin c)").parse()
            ('asin', ('c'))

            sage: SEXParser("(pi)").parse()
            ('pi', ())

            sage: f = fricas('(x + y/2)::DMP(["x", "y", "z"], FRAC INT)')
            sage: i = fricas.get_InputForm(f"dom({f._name})::Any")
            sage: SEXParser(i, raw=True).parse()
            ('DistributedMultivariatePolynomial',
             ('x', 'y', 'z'),
             ('Fraction', ('Integer',)))
        """
        a = self._start
        while self._s[a] in self._WHITESPACE:
            a += 1

        self._start = a
        if self._s[a] == self._LEFTBRACKET:
            return self._parse_list()
        if self._s[a] == self._STRINGMARKER:
            return self._parse_string()
        return self._parse_atom()

    def _parse_list(self):
        """
        Parse the initial part of a string, assuming that it is a
        whitespace separated list.

        TESTS::

            sage: from sage.interfaces.fricas_translator import SEXParser
            sage: SEXParser("()").parse()
            ('', ())

            sage: SEXParser("(a b c)").parse()
            ('a', ('b', 'c'))

            sage: SEXParser('(bcd)').parse()
            ('bcd', ())
        """
        # self._start specifies the position of the left bracket
        assert self._s[self._start] == self._LEFTBRACKET
        self._start += 1

        if not self._raw:
            self._raw = True
            head = self._parse_atom()
            self._raw = False
            self._start += 1

        args = []
        while self._s[self._start] != self._RIGHTBRACKET:
            e = self.parse()
            args.append(e)
            self._start += 1

        args = tuple(args)
        if not self._raw:
            return (head, args)
        return args

    def _parse_atom(self):
        """
        Parse the initial part of a string, assuming that it is an
        atom, but not a string.

        Symbols and numbers must not contain ``_WHITESPACE`` and
        ``_RIGHTBRACKET``.

        TESTS::

            sage: from sage.interfaces.fricas_translator import SEXParser
            sage: SEXParser("abc").parse()
            'abc'
            sage: SEXParser("123 xyz").parse()
            123
        """
        a = self._start
        b = len(self._s)

        while (a < b
               and self._s[a] not in self._WHITESPACE
               and self._s[a] != self._RIGHTBRACKET):
            a += 1

        token = self._s[self._start:a]

        self._start = a - 1
        if self._raw:
            return token

        try:
            return Integer(token)
        except TypeError:
            try:
                return float(token)
            except ValueError:
                return token

    def _parse_string(self):
        r"""
        Parse the initial part of a string, assuming that it represents a
        string.

        TESTS::

            sage: from sage.interfaces.fricas_translator import SEXParser
            sage: SEXParser('"abc" 123').parse()
            'abc'

            sage: SEXParser('"" 123').parse()
            ''

            sage: SEXParser('"____" 123').parse()
            '__'

            sage: SEXParser('"_a" 123').parse()
            'a'

            sage: SEXParser('"_" _"" 123').parse()
            '" "'

            sage: SEXParser('"(b c)"').parse()
            '(b c)'
        """
        a = self._start  # the position of the left quote
        assert self._s[a] == _STRINGMARKER
        b = a + 1
        a = b
        S = []

        while self._s[b] != _STRINGMARKER:
            if self._s[b] == _ESCAPEMARKER:
                S.append(self._s[a:b])
                b += 1
                a = b
            b += 1

        self._start = b
        S.append(self._s[a:b])
        return "".join(S)
