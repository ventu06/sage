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

    def __init__(self, parent, finite_part, infinite_part) -> None:
        raise NotImplementedError  # TODO

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

    def __init__(self, function_field, base_div, **kwds) -> None:
        super().__init__(function_field, base_div, **kwds)

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
