# Seed

Tengoku depends on nothing. It was SEEDED once from the following sources — their files were folded into the tree under topic paths, imports rewritten, declaration names untouched. After seeding, these origins have no relationship to Tengoku.

Toolchain: `leanprover/lean4:v4.34.0-rc2`

| package | origin | rev | mapped to |
|---|---|---|---|
| mathlib | https://github.com/leanprover-community/mathlib4.git | 85e3a25e006c35636f0e53b0e9296caca2685bc0 | `Tengoku.Seed` |
| batteries | https://github.com/leanprover-community/batteries | d54dddc581e08be364c278052863524bff7a99a9 | `Tengoku.Seed.Std` |
| aesop | https://github.com/leanprover-community/aesop | 18889deb9e83ea7420ef51c160d6f88552e744e3 | `Tengoku.Seed.Tactic.Aesop` |
| Qq | https://github.com/leanprover-community/quote4 | 507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3 | `Tengoku.Seed.Meta.Qq` |
| proofwidgets | https://github.com/leanprover-community/ProofWidgets4 | a8acbfd87375ff4abe14ce09db5b7664d383bc7f | `Tengoku.Seed.Widgets` |
| plausible | https://github.com/leanprover-community/plausible | d9598f07b1bc701f1e3aae163d2681c1fd978793 | `Tengoku.Seed.Testing.Random` |
| LeanSearchClient | https://github.com/leanprover-community/LeanSearchClient | ba67e212be1197b84c1f1f6299488a10a3002713 | `Tengoku.Seed.Search.LeanSearchClient` |
| importGraph | https://github.com/leanprover-community/import-graph | d8823026ac7ef130c253089d95685f9877b95323 | `Tengoku.Seed.Meta.ImportGraph` |
| Cli | https://github.com/leanprover/lean4-cli | ab3a82db9fea14cf0fd7f5a2de650f4b534640af | `Tengoku.Seed.Meta.Cli` |
