"""Paper 1.3.7 / O001 — IST response-independent legacy-channel obstruction.

O001 is an implementation-refactor blocker, not a universal mathematical no-go
result.  The legacy growth implementation contains response-independent scalar
channels that can alter the active birth data without consuming the C007
response or the M003 steering value.  The original audit covered only rank,
forward, and backward asymmetry.  The Tier-C review exposed five further
mechanism classes in the same legacy path:

* node-load scalars (environment, ancestor, sibling, child, and ``birth_g``);
* nonlinear mode transforms;
* fixed ancestor/sibling backreaction scales;
* additive unit baselines; and
* explicit depth/rank-distance attenuation.

The executable side therefore has two responsibilities:

1. audit executable Python AST nodes in the bound legacy source and identify
   the concrete response-independent mechanism classes rather than comments or
   documentation;
2. provide a falsifiable admission guard.  A candidate M004 dependency tuple
   carries the intended ``state``, ``slot``, ``response``, and ``steering``
   variables plus explicit presence flags.  Admission succeeds exactly when
   every forbidden legacy channel is absent.  The admitted tuple preserves the
   four intended inputs and drops the obstruction record entirely.

O001 does not choose the C015 transform, define M003, prove positivity of the
response-derived scalar, or execute C008.  It only closes the implementation
boundary before M004.
"""
from __future__ import annotations

import ast
import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Generic, TypeVar

StateT = TypeVar("StateT")
SlotT = TypeVar("SlotT")
ResponseT = TypeVar("ResponseT")
SteeringT = TypeVar("SteeringT")

CHANNEL_ORDER = (
    "rank",
    "forward",
    "backward",
    "node_load_scalar",
    "nonlinear_mode",
    "backreaction_scale",
    "additive_baseline",
    "geometric_attenuation",
)
LEGACY_SOURCE_SHA256 = "7b46297b6650fd9e5b9a10181746970de0dc1561d4fa7f4c938115f5f56f8099"
LEGACY_GROWTH_FUNCTIONS = (
    "_mode_scale",
    "_birth_environment_load",
    "_make_growth_step",
    "_base_birth_edge_weights",
    "_apply_growth_step",
    "_add_slot_sibling_relations",
)
# Historical name retained for callers; the audit now covers the complete
# response-independent legacy path rather than only directional functions.
LEGACY_DIRECTIONAL_FUNCTIONS = LEGACY_GROWTH_FUNCTIONS

# One executable symbol can witness multiple mechanism classes.
FORBIDDEN_SYMBOL_CHANNELS: dict[str, tuple[str, ...]] = {
    "sibling_rank": ("rank",),
    "rank_bias": ("rank",),
    "rank_distance": ("rank", "geometric_attenuation"),
    "forward_rank_bias": ("rank", "forward"),
    "backward_rank_bias": ("rank", "backward"),
    "backward_base": ("backward",),
    "sibling_forward_asym": ("forward",),
    "sibling_backward_asym": ("backward",),
    "env_birth_edge_bias": ("node_load_scalar",),
    "ancestor_node_load": ("node_load_scalar",),
    "sibling_node_load": ("node_load_scalar",),
    "child_env_load": ("node_load_scalar",),
    "birth_g": ("node_load_scalar",),
    "_mode_scale": ("nonlinear_mode",),
    "log1p": ("nonlinear_mode",),
    "mode": ("nonlinear_mode",),
    "ancestor_backreaction": ("backreaction_scale",),
    "sibling_backreaction": ("backreaction_scale",),
}

_RESPONSE_NAME_FRAGMENTS = (
    "response",
    "schur",
    "dtn",
    "steering",
    "sigma",
)


@dataclass(frozen=True, slots=True)
class IndependentDirectedBiasPresence:
    """Presence flags for every forbidden response-independent legacy channel."""

    rank: bool
    forward: bool
    backward: bool
    node_load_scalar: bool
    nonlinear_mode: bool
    backreaction_scale: bool
    additive_baseline: bool
    geometric_attenuation: bool

    @property
    def active_channels(self) -> tuple[str, ...]:
        return tuple(name for name in CHANNEL_ORDER if getattr(self, name))

    @property
    def is_removed(self) -> bool:
        return not self.active_channels


NO_INDEPENDENT_DIRECTED_BIAS = IndependentDirectedBiasPresence(
    rank=False,
    forward=False,
    backward=False,
    node_load_scalar=False,
    nonlinear_mode=False,
    backreaction_scale=False,
    additive_baseline=False,
    geometric_attenuation=False,
)

# Historical three-channel witness remains available and falsifiable.
LEGACY_RANK_FORWARD_BACKWARD_BIAS = IndependentDirectedBiasPresence(
    rank=True,
    forward=True,
    backward=True,
    node_load_scalar=False,
    nonlinear_mode=False,
    backreaction_scale=False,
    additive_baseline=False,
    geometric_attenuation=False,
)

# Full witness for the bound legacy growth implementation.
LEGACY_RESPONSE_INDEPENDENT_CHANNELS = IndependentDirectedBiasPresence(
    rank=True,
    forward=True,
    backward=True,
    node_load_scalar=True,
    nonlinear_mode=True,
    backreaction_scale=True,
    additive_baseline=True,
    geometric_attenuation=True,
)


@dataclass(frozen=True, slots=True)
class CandidateGrowthLawInputs(Generic[StateT, SlotT, ResponseT, SteeringT]):
    """Candidate M004 dependencies before the O001 removal gate."""

    state: StateT
    slot: SlotT
    response: ResponseT
    steering: SteeringT
    independent_bias: IndependentDirectedBiasPresence


@dataclass(frozen=True, slots=True)
class AdmittedGrowthLawInputs(Generic[StateT, SlotT, ResponseT, SteeringT]):
    """The only dependency tuple O001 permits downstream to M004."""

    state: StateT
    slot: SlotT
    response: ResponseT
    steering: SteeringT


class ResponseIndependentBiasError(ValueError):
    """Raised when a candidate still contains a forbidden independent channel."""


@dataclass(frozen=True, slots=True)
class LegacyBiasFinding:
    channel: str
    symbol: str
    function: str
    line: int


@dataclass(frozen=True, slots=True)
class LegacyBiasAudit:
    source_sha256: str
    findings: tuple[LegacyBiasFinding, ...]
    response_dependencies: tuple[str, ...]
    inspected_functions: tuple[str, ...]

    @property
    def active_channels(self) -> tuple[str, ...]:
        present = {finding.channel for finding in self.findings}
        return tuple(channel for channel in CHANNEL_ORDER if channel in present)

    @property
    def is_response_independent(self) -> bool:
        return not self.response_dependencies

    @property
    def obstruction_present(self) -> bool:
        return self.active_channels == CHANNEL_ORDER and self.is_response_independent


def admit_growth_law_inputs(
    candidate: CandidateGrowthLawInputs[StateT, SlotT, ResponseT, SteeringT],
) -> AdmittedGrowthLawInputs[StateT, SlotT, ResponseT, SteeringT]:
    """Remove the O001 channel record or reject the candidate explicitly."""
    if type(candidate) is not CandidateGrowthLawInputs:
        raise TypeError("O001 requires CandidateGrowthLawInputs")
    if type(candidate.independent_bias) is not IndependentDirectedBiasPresence:
        raise TypeError("O001 requires explicit independent-channel presence flags")
    active = candidate.independent_bias.active_channels
    if active:
        raise ResponseIndependentBiasError(
            "O001 rejects response-independent legacy channels: "
            + ", ".join(active)
        )
    return AdmittedGrowthLawInputs(
        state=candidate.state,
        slot=candidate.slot,
        response=candidate.response,
        steering=candidate.steering,
    )


def _function_symbol_references(
    function: ast.FunctionDef | ast.AsyncFunctionDef,
) -> list[tuple[str, int]]:
    references: list[tuple[str, int]] = []
    for node in ast.walk(function):
        if isinstance(node, ast.Attribute):
            references.append((node.attr, node.lineno))
        elif isinstance(node, ast.Name):
            references.append((node.id, node.lineno))
    return references


def _target_names(node: ast.AST) -> tuple[str, ...]:
    if isinstance(node, ast.Name):
        return (node.id,)
    if isinstance(node, (ast.Tuple, ast.List)):
        return tuple(name for element in node.elts for name in _target_names(element))
    return ()


def _contains_numeric_one(node: ast.AST) -> bool:
    return any(
        isinstance(part, ast.Constant)
        and type(part.value) in (int, float)
        and float(part.value) == 1.0
        for part in ast.walk(node)
    )


def _contains_addition(node: ast.AST) -> bool:
    return any(isinstance(part, ast.BinOp) and isinstance(part.op, ast.Add) for part in ast.walk(node))


def _synthetic_findings(
    function_name: str,
    function: ast.FunctionDef | ast.AsyncFunctionDef,
) -> list[LegacyBiasFinding]:
    findings: list[LegacyBiasFinding] = []
    for node in ast.walk(function):
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            target_names = {name for target in targets for name in _target_names(target)}
            value = node.value
            if target_names.intersection({"w0", "birth_g"}) and _contains_numeric_one(value) and _contains_addition(value):
                findings.append(
                    LegacyBiasFinding(
                        channel="additive_baseline",
                        symbol="additive_unit_baseline",
                        function=function_name,
                        line=node.lineno,
                    )
                )
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            names = {
                part.id
                for part in ast.walk(node)
                if isinstance(part, ast.Name)
            }
            for witness in ("depth", "rank_distance"):
                if witness in names:
                    findings.append(
                        LegacyBiasFinding(
                            channel="geometric_attenuation",
                            symbol=witness,
                            function=function_name,
                            line=node.lineno,
                        )
                    )
    return findings


def audit_legacy_response_independent_bias(source: str) -> LegacyBiasAudit:
    """Audit executable AST nodes for the complete O001 legacy mechanism."""
    if not isinstance(source, str):
        raise TypeError("O001 source audit requires text")
    tree = ast.parse(source)
    functions = {
        node.name: node
        for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    findings: list[LegacyBiasFinding] = []
    response_dependencies: set[str] = set()
    inspected: list[str] = []

    for function_name in LEGACY_GROWTH_FUNCTIONS:
        function = functions.get(function_name)
        if function is None:
            continue
        inspected.append(function_name)
        for symbol, line in _function_symbol_references(function):
            for fragment in _RESPONSE_NAME_FRAGMENTS:
                if fragment in symbol.lower():
                    response_dependencies.add(symbol)
            for channel in FORBIDDEN_SYMBOL_CHANNELS.get(symbol, ()):
                findings.append(
                    LegacyBiasFinding(
                        channel=channel,
                        symbol=symbol,
                        function=function_name,
                        line=line,
                    )
                )
        findings.extend(_synthetic_findings(function_name, function))

    # AST traversal can encounter the same attribute both as an Attribute and as
    # the Name under a call.  Deduplicate by the externally meaningful record.
    findings = sorted(
        set(findings),
        key=lambda finding: (finding.line, finding.channel, finding.symbol, finding.function),
    )
    return LegacyBiasAudit(
        source_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
        findings=tuple(findings),
        response_dependencies=tuple(sorted(response_dependencies)),
        inspected_functions=tuple(inspected),
    )


def audit_legacy_response_independent_bias_file(path: str | Path) -> LegacyBiasAudit:
    source_path = Path(path)
    return audit_legacy_response_independent_bias(source_path.read_text(encoding="utf-8"))


__all__ = [
    "CHANNEL_ORDER",
    "LEGACY_SOURCE_SHA256",
    "LEGACY_GROWTH_FUNCTIONS",
    "LEGACY_DIRECTIONAL_FUNCTIONS",
    "FORBIDDEN_SYMBOL_CHANNELS",
    "IndependentDirectedBiasPresence",
    "NO_INDEPENDENT_DIRECTED_BIAS",
    "LEGACY_RANK_FORWARD_BACKWARD_BIAS",
    "LEGACY_RESPONSE_INDEPENDENT_CHANNELS",
    "CandidateGrowthLawInputs",
    "AdmittedGrowthLawInputs",
    "ResponseIndependentBiasError",
    "LegacyBiasFinding",
    "LegacyBiasAudit",
    "admit_growth_law_inputs",
    "audit_legacy_response_independent_bias",
    "audit_legacy_response_independent_bias_file",
]
