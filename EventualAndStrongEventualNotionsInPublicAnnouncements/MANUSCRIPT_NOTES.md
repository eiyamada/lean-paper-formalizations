# Manuscript notes

Source: `True_lies_and_impossible_lies/main.tex` in
`eiyamada/True_lies_and_impossible_lies`, commit
`49e893b419533ab577dce5424a567a98e58dbd06` (17 September 2026).
The manuscript itself has not been modified by this formalization.

1. **Remark 1, the common-belief language extension.** After replacing
   `SE_10 ↔ E_10` by `SE_10 → E_10`, the statement that all other
   equivalences remain valid needs qualification. The intended limit chain is
   `SE_10 ↔ (every trace converges to 0) → E_10 ↔ (every trace has liminf 0)`.
   Retaining the entire original limit chain would reinstate the removed
   equivalence. The formal statements keep the two equivalence pairs separate.
2. **Conclusion.** “Strong eventuality implies finite eventuality ... within
   both the finite and transfinite settings” should refer to the corresponding
   eventuality in each setting. Transfinite strong eventuality does not imply
   finite eventuality; the ordinal-return examples are counterexamples.
3. **Figure caption.** The caption referring to the one-peeling construction
   as the two-peeling model should be aligned with its definition.

No alteration of a numbered mathematical claim is proposed here. Proof
certificates establish precisely their Lean statements; the coverage map
records the connection to the manuscript.
