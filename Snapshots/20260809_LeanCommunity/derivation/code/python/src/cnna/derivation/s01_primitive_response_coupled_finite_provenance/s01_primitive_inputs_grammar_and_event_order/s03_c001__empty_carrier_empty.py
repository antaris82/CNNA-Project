"""Paper 1.1.3 / C001 — empty carrier ``∅``.

Scientific contract
-------------------
The derivation starts from one canonical carrier with exactly

    no provenance nodes and no relations.

This module represents that carrier as an inhabited zero-payload value.  It
must not be confused with Python's notion of a missing object, with ``None``,
or with the post-genesis rooted state constructed by C002.

No provenance-event order is introduced here.  Event ordering is owned by the
separate C018 node in the frozen DAG.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class EmptyCarrier:
    """The unique zero-payload value representing the pre-root carrier.

    The class has no dataclass fields.  Hence there is no stored node,
    relation, parameter, position, or hidden initialization payload at this
    derivation node.  Query methods expose the defining empty-carrier
    semantics explicitly for executable tests and downstream guards.
    """

    @property
    def nodes(self) -> tuple[object, ...]:
        """Return the empty provenance-node collection."""

        return ()

    @property
    def relations(self) -> tuple[tuple[object, object], ...]:
        """Return the empty relation collection."""

        return ()

    def contains_node(self, _node: object) -> bool:
        """No object is a provenance node of the empty carrier."""

        return False

    def contains_relation(self, _source: object, _target: object) -> bool:
        """No ordered pair is a relation of the empty carrier."""

        return False


EMPTY_CARRIER = EmptyCarrier()


__all__ = ["EMPTY_CARRIER", "EmptyCarrier"]
