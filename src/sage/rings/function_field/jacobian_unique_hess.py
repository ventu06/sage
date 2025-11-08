r"""
Jacobians in the Unique Hess model

This module implements Jacobian arithmetic based on divisor representation by
ideals, much like :mod:`sage.rings.function_field.jacobian_hess`.
This approach to Jacobian arithmetic implementation is attributed to Hess [Hes2002]_.

The Unique Hess variant implemented here is a modification due to Macri [Mac2025]_
of Hess' maximally reduced divisors, but with a linear search reduction algorithm
that performs better in practice when doing a sequence of many Jacobian arithmetic operations.

The Unique Hess model is the only Jacobian model implemented in Sage that uses unique
representatives of divisor classes. To the best of the author's knowledge at time of writing,
this module makes SageMath the only computer algebra system that includes a model of Jacobian
arithmetic that uses unique representatives of divisor classes.

Jacobian
--------

To create a Jacobian in the Unique Hess model, specify ``'unique_hess'`` model and provide a base place of degree 1.

AUTHORS:

- Vincent Macri (2025-10-10): initial version
"""

# ****************************************************************************
#       Copyright (C) 2025 Vincent Macri <vincent.macri@ucaglary.ca>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from __future__ import annotations

from typing import TYPE_CHECKING

from sage.misc.cachefunc import cached_method

from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.richcmp import op_EQ, op_NE, richcmp

from sage.categories.map import Map
from sage.categories.commutative_additive_groups import CommutativeAdditiveGroups
from sage.categories.homset import Hom

from sage.arith.misc import integer_ceil
from sage.arith.functions import lcm

from sage.rings.integer import Integer
from sage.matrix.constructor import matrix

from sage.combinat.integer_vector_weighted import WeightedIntegerVectors

from . import riemann_roch
from .place import FunctionFieldPlace
from .divisor import FunctionFieldDivisor

from .jacobian_base import (Jacobian_base,
                            JacobianGroup_base,
                            JacobianGroup_finite_field_base,
                            JacobianPoint_base,
                            JacobianPoint_finite_field_base)

if TYPE_CHECKING:
    from .function_field import FunctionField
    from .ideal import FunctionFieldIdealInfinite, FunctionFieldIdeal
    FunctionFieldIdealFinite = FunctionFieldIdeal  # For readability when we specifically mean a finite ideal

class JacobianPoint(JacobianPoint_base):

    def __init__(self, parent: JacobianGroup, finite_ideal: FunctionFieldIdealFinite,
                 infinite_ideal: FunctionFieldIdealInfinite) -> None:
        super().__init__(parent)
        self._finite_ideal, self._infinite_ideal, self._r = parent._reduce(finite_ideal, infinite_ideal)

    def __hash__(self) -> int:
        raise NotImplementedError  # TODO

    def _richcmp_(self, other, op):
        if not isinstance(other, JacobianPoint) or other.parent() != self.parent():
            return op == op_NE

        equal = (self._finite_ideal == other._finite_ideal) and (self._infinite_ideal == other._infinite_ideal)
        if op is op_EQ:
            return equal
        elif op is op_NE:
            return not equal
        return NotImplemented

    def _add_(self, other):
        # TODO: Docstring
        G = self.parent()
        D = G.element_class(G,
                            self._finite_ideal * other._finite_ideal,
                            G._infinite_ideal_mult(self._infinite_ideal, other._infinite_ideal)
                            )
        return D

    def _neg_(self):
        raise NotImplementedError  # TODO

    def multiple(self, n):
        raise NotImplementedError  # TODO

    def order(self):
        """
        Return the order of this point.
        """
        # TODO: Implement with hash tables
        raise NotImplementedError  # TODO

    def effective_part(self):
        raise NotImplementedError  # TODO

    def divisor(self) -> FunctionFieldDivisor:
        return (~self._finite_ideal).divisor() + (~self._infinite_ideal).divisor()


class JacobianPoint_finite_field(JacobianPoint, JacobianPoint_finite_field_base):
    pass

class JacobianGroupEmbedding(Map):
    pass

class JacobianGroup(UniqueRepresentation, JacobianGroup_base):
    Element = JacobianPoint

    def __init__(self, parent, function_field, base_div: FunctionFieldDivisor) -> None:

        super().__init__(parent, function_field, base_div)

        A = parent._A
        if not base_div == A:
            raise ValueError('base_div must equal base_place')

        # We use inverted ideals, so _A_inv is actually the uninverted place
        self._A_inv = A.prime_ideal()
        self._A = self._A_inv.inverse()
        self._A_g_minus_1 = self._A ** (self._genus - 1)

        # For faster/more convenient access from the JacobianPoint class
        self._vector_space, self._from_vector_space, self._to_vector_space = self._function_field.free_module(map=True)
        self._A_is_infinite = A.is_infinite_place()
        self._function_field_degree = self._function_field.degree()
        self._maximal_order_finite = self._function_field.maximal_order()
        self._maximal_order_infinite = self._function_field.maximal_order_infinite()

        if parent._cache_infinite_ideals:
            self._infinite_ideal_mult = self._cached_ideal_mult
            self._inverse_infinite_matrix = self._cached_inverse_infinite_matrix
        else:
            self._infinite_ideal_mult = lambda J1, J2: J1 * J2
            self._inverse_infinite_matrix = lambda J : matrix([self._to_vector_space(b) for b in J.gens_over_base()]).inverse()

        # Ideal multiplication is expensive, so we want to avoid unnecessary multiplication by identity.
        # We define functions to handle this so that we don't need to complicate our reduction logic with branching.
        if self._A_is_infinite:
            self._multiply_pair_by_A = lambda I, J, A : (I, self._infinite_ideal_mult(J, A))
        else:
            self._multiply_pair_by_A = lambda I, J, A : (I * A, J)

    def _reduce(self, I: FunctionFieldIdealFinite, J: FunctionFieldIdealInfinite) -> tuple[FunctionFieldIdealFinite, FunctionFieldIdealInfinite, int]:
        # We take the input divisor D and find the maximal r such that ℓ(D + rA) = 1
        degree = self._function_field_degree
        to = self._to_vector_space

        def matrices_and_riemann_roch(C, B_inv, tilde_I, tilde_J):
            if self._A_is_infinite:
                B_inv = self._inverse_infinite_matrix(tilde_J)
                return C, B_inv, riemann_roch._short_circuit_riemann_roch_matrices(degree, C, B_inv, tilde_I.gens_over_base())
            else:
                C = matrix([to(v) for v in tilde_I.gens_over_base()])
                return C, B_inv, riemann_roch._short_circuit_riemann_roch_matrices(degree, C, B_inv, tilde_I.gens_over_base())

        tilde_I, tilde_J = self._multiply_pair_by_A(I, J, self._A_g_minus_1)
        C = matrix([to(v) for v in tilde_I.gens_over_base()])
        B_inv = self._inverse_infinite_matrix(tilde_J)

        last_basis = riemann_roch._short_circuit_riemann_roch_matrices(degree, C, B_inv, tilde_I.gens_over_base())

        if last_basis is None:  # ell(D + (g - 1) A) = 0
            r = self._genus
            tilde_I, tilde_J = self._multiply_pair_by_A(tilde_I, tilde_J, self._A)  # D + gA
            C, B_inv, basis = matrices_and_riemann_roch(C, B_inv, tilde_I, tilde_J)
        else:
            r = 0
            last_tilde_I, last_tilde_J = tilde_I, tilde_J
            for n in range(self._genus - 2, -1, -1):
                tilde_I, tilde_J = self._multiply_pair_by_A(tilde_I, tilde_J, self._A_inv)  # D + nA
                C, B_inv, basis = matrices_and_riemann_roch(C, B_inv, tilde_I, tilde_J)
                if basis is None:
                    # ℓ(D + nA) = 0, hence ℓ(D + (n + 1) A) = 1
                    basis = last_basis
                    r = n + 1
                    tilde_I, tilde_J = last_tilde_I, last_tilde_J
                    break
                last_tilde_I, last_tilde_J = tilde_I, tilde_J
                last_basis = basis
            # If we never hit the breakpoint then ℓ(D) = 1, which happens iff D = 0

        f_inv = ~basis

        fI = self._maximal_order_finite.ideal(f_inv)
        fJ = self._maximal_order_infinite.ideal(f_inv)

        return I * fI, self._cached_ideal_mult(J, fJ), r

    @cached_method
    def _cached_inverse_infinite_matrix(self, J):
        return matrix([self._to_vector_space(b) for b in J.gens_over_base()]).inverse()

    @cached_method(key=lambda self, J1, J2 : frozenset((J1, J2)))
    def _cached_ideal_mult(self, J1: FunctionFieldIdealInfinite, J2: FunctionFieldIdealInfinite):
        # TODO: Docstring
        return J1 * J2

    def _element_constructor_(self, x):
        if x == 0:
            return self.zero()

        if isinstance(x, FunctionFieldPlace):
            x = x.divisor()

        if isinstance(x, FunctionFieldDivisor) and x in self._function_field.divisor_group():
            return self.point(x)

        raise ValueError(f'cannot construct a point from {x}')

    def point(self, divisor: FunctionFieldDivisor):
        """
        Return the point represented by the divisor of degree zero.
        """
        if divisor.degree() != 0:
            raise ValueError('divisor not of degree zero')
        I, J = riemann_roch._divisor_to_inverted_ideals(divisor)
        return self.element_class(self, I, J)

    @cached_method
    def zero(self):
        """
        Return the zero element of this group.
        """
        return self.point(self._function_field.divisor_group().zero())

    def _repr_(self) -> str:
        """
        Return the string representation of ``self``.
        """
        return f'{super()._repr_()} (Unique Hess model)'

    def __iter__(self):
        """
        Return generator of points of this group.
        """
        # TODO: Temporary implementation, does give all elements
        for D in self._function_field.divisor_group().some_elements():
            newD = D - self._base_div * D.degree()
            assert newD.degree() == 0
            yield self.point(newD)

class JacobianGroup_finite_field(JacobianGroup, JacobianGroup_finite_field_base):
    Element = JacobianPoint_finite_field

class Jacobian(Jacobian_base, UniqueRepresentation):
    pass

    def __init__(self, function_field, base_div: FunctionFieldDivisor | FunctionFieldPlace, cache_infinite_ideals: bool = True, **kwds) -> None:
        """
        TESTS::

            sage: K = GF(11)
            sage: Kx.<x> = FunctionField(K)
            sage: t = polygen(Kx)
            sage: F.<y> = Kx.extension(t^4 + 9*x*t^3 + (10*x + 7)*t^2 + (7*x^2 + 2*x + 10)*t + 9*x^3 + 3*x^2 + 6*x + 4)
            sage: J = F.jacobian(model='unique_hess')
            sage: TestSuite(J).run()
        """

        if base_div.degree() != 1:
            raise ValueError('base_div must be degree 1')

        if isinstance(base_div, FunctionFieldPlace):
            super().__init__(function_field, base_div.divisor(), **kwds)
            self._A = base_div
        elif isinstance(base_div, FunctionFieldDivisor):  # Allowed for compatibility with other Jacobian models
            if not base_div.is_prime():
                raise ValueError('base_div must be a prime divisor')
            super().__init__(function_field, base_div, **kwds)
            self._A = base_div.place()
        else:
            raise TypeError('base_div must be a divisor or a place')

        self._cache_infinite_ideals = cache_infinite_ideals

        if function_field.constant_base_field().is_finite():
            self._group_class = JacobianGroup_finite_field
        else:
            self._group_class = JacobianGroup

    def _repr_(self) -> str:
        """
        Return the string representation of ``self``.
        """
        # TODO: Add tests
        return f'{super()._repr_()} (Unique Hess model)'

    def _latex_(self) -> str:
        # TODO: Docstring
        return fr'\operatorname{{Cl}}^0 ( {self._function_field._latex_()} ) \text{{(Unique Hess model)}}'
