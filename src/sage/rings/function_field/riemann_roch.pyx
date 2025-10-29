r"""
Utility functions for Riemann-Roch computations.

AUTHORS:

- Vincent Macri (2025-10-29): initial version, based on refactored code by Kwankyu Lee
"""

# ****************************************************************************
#       Copyright (C) 2017-2022 Kwankyu Lee <ekwankyu@gmail.com>
#                     2025      Vincent Macri <vincent.macri@ucalgary.ca>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.arith.functions import lcm  # Should we use LCM_list or make lcm cpdef?
from sage.matrix.matrix cimport Matrix

cpdef short_circuited_riemann_roch(F, I, J):  # TODO: Update docstring
    """
    Return a pair of normalized ideals from `I` and `J`.

    INPUT:

    - ``I`` -- an ideal of the finite maximal order

    - ``J`` -- an ideal of the infinite maximal order

    The output represents an effective divisor linearly equivalent to the
    divisor represented by the given ideals `I` and `J`.

    ALGORITHM:

    Computes a function `f` in the Riemann-Roch space of the divisor `D`
    represented by the (inverted) ideals `I` and `J`. The output is the
    pair of the (inverted) ideals representing the effective divisor `(f) + D`,
    which is linearly equivalent to `D`.

    TESTS::

        sage: k = GF(17)
        sage: P2.<x,y,z> = ProjectiveSpace(k, 2)
        sage: C = Curve(x^3 + 5*z^3 - y^2*z, P2)
        sage: b = C([0,1,0]).place()
        sage: J = C.jacobian(model='hess', base_div=b)
        sage: G = J.group()
        sage: pl = C([2,8,1]).place()
        sage: p = G.point(pl - b)
        sage: dS, ds = (p + p)._data  # indirect doctest
        sage: G.point((~dS).divisor() + (~ds).divisor() - b) == p + p
        True
    """
    n = F.degree()

    O = F.maximal_order()
    Oinf = F.maximal_order_infinite()

    # Step 1: construct matrix M of rational functions in x such that
    # M * B == C where B = [b1,b1,...,bn], C =[v1,v2,...,vn]
    V, fr, to = F.free_module(map=True)
    B = Matrix([to(b) for b in J.gens_over_base()])
    C = Matrix([to(v) for v in I.gens_over_base()])
    M = C * B.inverse()

    # Step 2: get the denominator d of M and set mat = d * M
    den = lcm([e.denominator() for e in M.list()])
    R = den.parent()  # polynomial ring
    one = R.one()
    mat = Matrix(R, n, [e.numerator() for e in (den * M).list()])
    gens = list(I.gens_over_base())

    # Step 3: transform mat to a weak Popov form, together with gens

    # initialise pivot_row and conflicts list
    found = None
    pivot_row = [[] for i in range(n)]
    conflicts = []
    for i in range(n):
        bestp = -1
        best = -1
        for c in range(n):
            d = mat[i, c].degree()
            if d >= best:
                bestp = c
                best = d

        if best <= den.degree():
            found = i
            break

        if best >= 0:
            pivot_row[bestp].append((i, best))
            if len(pivot_row[bestp]) > 1:
                conflicts.append(bestp)

    if found is None:
        # while there is a conflict, do a simple transformation
        while conflicts:
            c = conflicts.pop()
            row = pivot_row[c]
            i, ideg = row.pop()
            j, jdeg = row.pop()

            if jdeg > ideg:
                i, j = j, i
                ideg, jdeg = jdeg, ideg

            coeff = - mat[i, c].lc() / mat[j, c].lc()
            s = coeff * one.shift(ideg - jdeg)

            mat.add_multiple_of_row(i, j, s)
            gens[i] += s * gens[j]

            row.append((j, jdeg))

            bestp = -1
            best = -1
            for c in range(n):
                d = mat[i, c].degree()
                if d >= best:
                    bestp = c
                    best = d

            if best <= den.degree():
                found = i
                break

            if best >= 0:
                pivot_row[bestp].append((i, best))
                if len(pivot_row[bestp]) > 1:
                    conflicts.append(bestp)
        else:
            return None

    f = gens[found]
    #return (O.ideal(~f) * I, Oinf.ideal(~f) * J)
    return f
