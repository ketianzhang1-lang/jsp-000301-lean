# Power-family supplement under development

This is an extension of the same JSP-000390 contribution, not a separate prize request.
It preserves the earlier k=-1 source and intends to prove the whole known k=2^i family,
for every positive natural i. It does not resolve the original all-k question.

## Mathematical sources and contribution

Graham, D. H. Lehmer and E. Lehmer retain credit for the known family, as recorded by
the prize catalog. Quanyu Tang's public note, Section 3 / Theorem 3.1, explains the
n=i*p construction:
https://github.com/QuanyuTang/Erdos-Problem-479-Note/blob/7bd6cccea4b2ad023a334ff78bf4bef0b3366a0d/A_note_on_Erdos_Problem_479.tex

The new Lean module uses finite-monoid eventual periodicity in ZMod i to handle all
prime-power factors at once, including nonunits. Mathlib's elementary theorem of
infinitely many primes congruent to one supplies p; Fermat's theorem and the coprime
modulus combination finish the proof. The general-base result is proved as a useful
lemma; no new mathematical-discovery priority is claimed.

Prepared with OpenAI ChatGPT assistance at the submitting account's direction.
Existing Lean k=2 proofs and the previously inspected unproved all-powers assertion
in rjwalters/lean-genius remain prior art; no code from them is copied. Bounded public
searches cannot establish global priority. Prize eligibility remains for the organizers.

## Verification status

This file precedes the first actual build of the new module. No successful verification
is asserted here. The project fixes Lean and Mathlib to 4.34.0 with the existing manifest.
Run bash scripts/verify_power.sh and bash scripts/verify_power_nanoda.sh after acquiring
the locked dependencies. The workflow publishes actual logs and rejects out-of-policy
axioms. The original source and submitted PR are not changed until the supplement passes.
