# Porting Notes

This repository was originally written in Lean 3. During the Lean 4 port we
replace the following core list operations.

- `List.join` → `List.flatten`
- `List.nth_le` → `List.get`

The rewrites in `src/Grammars/Utilities/WrittenByOthers/ListTakeJoin.lean`
follow this mapping and should serve as a template for future translations.
