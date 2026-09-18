# Contribution and source provenance

We prepared the original `JSP000140.lean` under GitHub account
`ketianzhang1-lang`, with OpenAI ChatGPT/Codex assistance. It remains
byte-identical to proof branch commit `b9c7f4e9dfe6b9f398533b02c4b93805e1abc8f1`,
with SHA-256 `e41cf87887310cfbc9a1c83e70e090ddc790e35e6c504b16599b39360180060d`.
Its 22 public lemmas/theorems prove fork uniqueness and packing, colour-incidence
bounds, impossibility of equality, integer rounding and the four-vertex-set
formulation. This original source does not import plby/lean-proofs.

Our new bridge and endpoint add 22 public theorems. We construct conversions
between symmetric pair colourings and genuine unordered-edge labelings, identify
the minimum palette sizes for n >= 2, retain the strict finite lower bound and
connect the full asymptotic and eventual colourings to our original definition.
We also prepare the pinned source closure, compatibility port and verification.
The limit is transported from the existing complete asymptotic proof, which
also includes its own classical lower-bound argument. Our unchanged strict
finite lower theorem is an additional conclusion of the combined endpoint.

The lower-bound mathematics is classical, attributed to Erdős–Gyárfás and
Erdős–Elekes–Füredi. The complete asymptotic answer is due to Bennett, Cushman,
Dudek and Prałat, [Theorem 1](https://arxiv.org/html/2207.02920v1).
The reused construction development also uses the [Joos–Mubayi matching approach](https://arxiv.org/abs/2208.12563)
and the conflict-free matching framework named in its source headers; those
credits are retained. No new informal mathematical theorem is claimed.

The complete upper development is reused from plby/lean-proofs at
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Its entry credits Codex and GPT-5.6 Sol;
its modules retain their OpenAI Codex author notices and Apache 2.0 licenses.
UPSTREAM.json includes exactly 20 transitive dependencies. BernoulliFreedman
and Pippenger are not dependencies of the selected endpoint and are not imported.
Original URLs, Git blob hashes, SHA-256 hashes, mechanical compatibility edits
and ported-source SHA-256 hashes are recorded. The upstream license notice and
Apache license text accompany the package. Mathlib, exporter and NaNoda authors
retain their own credits and licenses.

We request review of our own formalization and integration work. The existing
complete public upper proof is disclosed irrespective of whether its authors
have entered the prize. We do not claim that imported proof as our original
work, first-formalization priority, organizer approval or award entitlement.
