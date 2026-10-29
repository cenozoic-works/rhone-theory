# rhone-theory

Population genetics in Lean 4 over Mathlib.

Results are attributed to models from OpenAI, Anthropic, Meta, internal models, and human experts.

| Path | Content |
|---|---|
| `Rhone/` | Lean library, one directory per area of mathematics |
| `Rhone/Unproved/` | statements without proofs; not in the default target |
| `Palomar/` | registry entries |
| `graph/bib/rhone.bib` | bibliography |

```
lake exe cache get
lake build
```

Lean and Mathlib `v4.35.0-rc3`.

Depends on [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache-2.0) and
[`vltanh/lean4-adr11`](https://github.com/vltanh/lean4-adr11) by The-Anh Vu-Le (Apache-2.0),
bridged in `Rhone/Statistics/External/`.

Pull requests are not accepted. Report problems through the issue tracker; see
[SECURITY.md](SECURITY.md).

Apache-2.0. See [LICENSE](LICENSE) and [CITATION.cff](CITATION.cff).
