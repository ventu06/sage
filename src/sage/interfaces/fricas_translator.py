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
            sage: ast = SEXParser("(1 2 3)").parse()
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
            sage: ast = SEXParser("(3 2)").parse()
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
            sage: ast = SEXParser("((1 2) (3 4))").parse()
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

        f, *args = self._ast
        try:
            fun = symbol_table["fricas"][(f, len(args))]
        except KeyError:
            try:
                fun = symbol_table["fricas"][(f, -1)]
            except KeyError:
                fun = function(f)

        args_eval = [SEXEvaluator(a, self._dom)._eval_sr_aux() for a in args]
        return fun(*args_eval)

    def _eval_sr(self):
        r"""
        Evaluate as element of the symbolic ring.
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

    def __init__(self, s):
        """
        INPUT:

        - ``s`` -- string
        """
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
            ('asin', 'c')

            sage: SEXParser("(pi)").parse()
            ('pi',)

            sage: f = fricas('(x + y/2)::DMP(["x", "y", "z"], FRAC INT)')
            sage: i = fricas.get_InputForm(f"dom({f._name})::Any")
            sage: SEXParser(i).parse()
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
            ()

            sage: SEXParser("(a b c)").parse()
            ('a', 'b', 'c')

            sage: SEXParser('(bcd)').parse()
            ('bcd',)
        """
        # self._start specifies the position of the left bracket
        assert self._s[self._start] == self._LEFTBRACKET
        self._start += 1

        args = []
        while self._s[self._start] != self._RIGHTBRACKET:
            e = self.parse()
            args.append(e)
            self._start += 1

        return tuple(args)

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
        assert self._s[a] == self._STRINGMARKER
        b = a + 1
        a = b
        S = []

        while self._s[b] != self._STRINGMARKER:
            if self._s[b] == self._ESCAPEMARKER:
                S.append(self._s[a:b])
                b += 1
                a = b
            b += 1

        self._start = b
        S.append(self._s[a:b])
        return "".join(S)
