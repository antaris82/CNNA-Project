"""Paper 1.1.4 / C002 — root genesis ``r``.

Scientific contract
-------------------
Starting from the canonical C001 empty carrier, root genesis creates one
and only one provenance node.  No relation exists at this stage.  The root has
no parent and no geometric position.

This node intentionally does *not* assign an address, numerical node id,
sibling rank, event index, conductance, load, or response datum.  Those data
are owned by later SOLL nodes in the frozen DAG.
"""

from __future__ import annotations

from dataclasses import dataclass

from .s03_c001__empty_carrier_empty import EmptyCarrier


@dataclass(frozen=True, slots=True)
class Root:
    """The unique zero-payload root token introduced by root genesis."""


ROOT = Root()


@dataclass(frozen=True, slots=True)
class RootedCarrier:
    """Canonical post-genesis carrier containing exactly the root and no edge."""

    @property
    def nodes(self) -> tuple[Root, ...]:
        return (ROOT,)

    @property
    def relations(self) -> tuple[tuple[Root, Root], ...]:
        return ()

    def contains_node(self, node: object) -> bool:
        return node == ROOT

    def contains_relation(self, _source: object, _target: object) -> bool:
        return False

    def parent_of(self, node: Root) -> None:
        if node != ROOT:
            raise ValueError("C002 contains only the canonical root")
        return None


ROOTED_CARRIER = RootedCarrier()


def root_genesis(carrier: EmptyCarrier) -> RootedCarrier:
    """Perform the unique C001 -> C002 genesis transition.

    The argument must be an ``EmptyCarrier`` value.  Since C001 has only
    one semantic inhabitant, the result is the canonical rooted carrier.
    """

    if type(carrier) is not EmptyCarrier:
        raise TypeError("root genesis requires the C001 EmptyCarrier")
    return ROOTED_CARRIER


__all__ = ["ROOT", "ROOTED_CARRIER", "Root", "RootedCarrier", "root_genesis"]
