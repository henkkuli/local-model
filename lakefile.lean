import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.7.0"

-- meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "bump-4.6"

package «da».«pn» where
  -- add package configuration options here

lean_lib «da».«pn» where
  -- add library configuration options here
