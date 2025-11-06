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

from sage.misc.cachefunc import cached_method

from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.richcmp import op_EQ, richcmp

from sage.categories.map import Map
from sage.categories.commutative_additive_groups import CommutativeAdditiveGroups
from sage.categories.homset import Hom

from sage.arith.misc import integer_ceil
from sage.arith.functions import lcm

from sage.rings.integer import Integer
from sage.rings.function_field import riemann_roch
from sage.matrix.constructor import matrix

from sage.combinat.integer_vector_weighted import WeightedIntegerVectors

from .place import FunctionFieldPlace
from .divisor import FunctionFieldDivisor

from .jacobian_base import (Jacobian_base,
                            JacobianGroup_base,
                            JacobianGroup_finite_field_base,
                            JacobianPoint_base,
                            JacobianPoint_finite_field_base)

class JacobianPoint(JacobianPoint_base):

    def __init__(self, parent, finite_ideal, infinite_ideal) -> None:
        super().__init__(parent)
        self._finite_ideal, self._infinite_ideal, self._n, a = self._reduce(finite_ideal, infinite_ideal)

    def _reduce(self, I, J):
        parent = self.parent()
        g = parent._genus
        return I, J, 0, 0

    def _repr_(self) -> str:
        raise NotImplementedError

    def __hash__(self) -> int:
        raise NotImplementedError  # TODO

    def _richcmp_(self, other, op):
        raise NotImplementedError  # TODO

    def _add_(self, other):
        raise NotImplementedError  # TODO

    def _neg_(self):
        raise NotImplementedError  # TODO

    def multiple(self, n):
        raise NotImplementedError  # TODO

    def divisor(self) -> FunctionFieldDivisor:
        raise NotImplementedError  # TODO

    def order(self):
        """
        Return the order of this point.
        """
        # TODO: Implement with hash tables
        raise NotImplementedError  # TODO

    def effective_part(self):
        raise NotImplementedError  # TODO

    def divisor(self):
        raise NotImplementedError  # TODO


class JacobianPoint_finite_field(JacobianPoint, JacobianPoint_finite_field_base):
    pass

class JacobianGroupEmbedding(Map):
    pass

class JacobianGroup(UniqueRepresentation, JacobianGroup_base):
    Element = JacobianPoint

    def __init__(self, parent, function_field, base_div) -> None:
        super().__init__(parent, function_field, base_div)

        # For faster/more convenient access from the JacobianPoint class
        self._vector_space, self._from_vector_space, self._to_vector_space = self._function_field.free_module(map=True)

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
        raise NotImplementedError  # TODO

    def _latex_(self) -> str:
        raise NotImplementedError  # TODO

    def __iter__(self):
        """
        Return generator of points of this group.
        """

        # TODO: Temporary implementation, does give all elements
        for D in self._function_field.divisor_group().some_elements():
            yield self.point(D - self._base_div * D.degree())

class JacobianGroup_finite_field(JacobianGroup, JacobianGroup_finite_field_base):
    Element = JacobianPoint_finite_field

class Jacobian(Jacobian_base, UniqueRepresentation):
    pass

    def __init__(self, function_field, base_div: FunctionFieldDivisor | FunctionFieldPlace, **kwds) -> None:
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

            # self._base_place would be a better name but is it already used for
            # something else in Jacobian_base. Also, the set_base_place method in
            # Jacobian_base allows self._base_place to be changed after construction,
            # which would cause us problems.
            # We call this value A to match with the literature that this implementation is based on.
            self._A = base_div
        elif isinstance(base_div, FunctionFieldDivisor):  # Allowed for compatibility with other Jacobian models
            if not base_div.is_prime():
                raise ValueError('base_div must be a prime divisor')
            super().__init__(function_field, base_div, **kwds)
            self._A = base_div.place()
        else:
            raise TypeError('base_div must be a divisor or a place')

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
