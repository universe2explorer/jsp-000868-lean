import Lake
open Lake DSL

package jsp000868 where
  -- Local proof repository for the Justin Sun Prize problem JSP-000868.
  -- See README.md and ../hidden_files/statement-correspondence.md.

@[default_target]
lean_lib JSP000868

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"
