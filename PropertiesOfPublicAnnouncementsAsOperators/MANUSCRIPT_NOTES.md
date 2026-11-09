# Source and interpretation notes

The formalization targets manuscript commit
[`3cc277515ae735f55c299d661a219452d7fff4b5`](https://github.com/eiyamada/Properties_of_PAL_and_BPAL_Operators/commit/3cc277515ae735f55c299d661a219452d7fff4b5),
dated 9 November 2026. This is the author's revision supplied during the
formalization. The manuscript itself is not modified by this development.

1. **Definition 5, revised BPAL order.** The revision distinguishes induced
   submodels from the broader BPAL order. `BPALSubmodel` allows a smaller domain
   and fewer arrows, with the restricted valuation. `ArrowSubmodel` is the
   same-domain special case used to represent an actual BPAL orbit. Both are
   present, and the operator-monotonicity and greatest-fixed-point results are
   proved for the broader order.
2. **Definition 22, admissible iteration.** Actual BPAL iteration and sequential
   BPAL composition preserve the initial world type and valuation. The
   intersection at limits therefore retains those fields without restoring
   any deleted states. PAL iteration takes intersections of surviving domains.
3. **Theorem 24, language restriction.** The formal rank comparisons and bounds
   use static epistemic formulas, matching the revised statement. PAL and BPAL
   have different dynamic announcement syntax and semantics; their separate
   reductions are not identified merely because an announcement symbol looks
   similar on the page.
4. **Pointwise versus uniform stabilization.** Ranks are defined per initial
   model. A global bound is an additional quantified assertion. In particular,
   the finite-uniform theorem proves the change in quantifier order using
   disjoint unions; arbitrary-ordinal witnesses rule out a uniform ordinal
   bound for the witness formula over all carriers.
5. **Fixed-point joins.** The formal statements prove greatest fixedness
   explicitly. For PAL the join is the union of fixed surviving domains; for
   BPAL the arrow relation is the union of relations of fixed models below the
   input at its fixed domain and valuation. The broader-domain greatest-fixed-
   point statement is proved separately as well.
6. **Frame-relative equality and empty sequences.** Algebraic equalities concern
   updates of input models in the selected frame class. Updates need not stay
   in that class. Sequence functions use lists, with the empty list acting as
   the identity.

The proofs sometimes use stronger or differently organized intermediate
statements. For example, the image-finite argument requires no finite-agent
type, and the incoming-predecessor argument equates global PAL and BPAL bounds
at every fixed ordinal. The coverage map states the representation and scope
of each result; prose literature summaries and proposed future research are
not additional formalized theorems.
