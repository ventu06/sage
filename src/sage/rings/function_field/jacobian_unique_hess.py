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
        self._finite_ideal, self._infinite_ideal, self._n, a = self._fast_reduce(finite_ideal, infinite_ideal)

    def _reduce(self, I, J):
        parent = self.parent()
        g = parent._genus

    def __hash__(self) -> int:
        raise NotImplementedError  # TODO

    def divisor(self) -> FunctionFieldDivisor:
        raise NotImplementedError  # TODO

    def _richcmp_(self, other, op):
        raise NotImplementedError  # TODO

    def _add_(self, other):
        raise NotImplementedError  # TODO

    def order(self):
        """
        Return the order of this point.
        """
        # TODO: Implement with hash tables
        raise NotImplementedError  # TODO

class JacobianPoint_finite_field(JacobianPoint, JacobianPoint_finite_field_base):

class JacobianGroupEmbedding(Map):
    pass

class JacobianGroup(UniqueRepresentation, JacobianGroup_base):
    pass

class JacobianGroup_finite_field(JacobianGroup, JacobianGroup_finite_field_base):
    Element = JacobianPoint_finite_field

class Jacobian(Jacobian_base, UniqueRepresentation):
    pass

    def __init__(self, function_field, base_div: FunctionFieldDivisor | FunctionFieldPlace, **kwds) -> None:

        if isinstance(base_div, FunctionFieldPlace)
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


        # For faster/more convenient access from the JacobianPoint class
        self._genus = self._function_field.genus()
        self._vector_space, self._from_vector_space, self._to_vector_space = self._function_field.free_module(map=True)

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
