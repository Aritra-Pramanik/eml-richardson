# EML trees: zero-equivalence and root existence are undecidable

A Lean 4 + Mathlib formalization of the reduction

> **Richardson's zero problem ≤ EML zero problem**

for the single binary operator **eml(x, y) = exp x − ln y**
([arXiv:2603.21852](https://arxiv.org/abs/2603.21852)). Together with the constant 1
and the variable x, this operator generates all elementary functions.

Assuming Richardson's theorem, the file proves that both of these problems are undecidable:

- **Zero-equivalence:** is a given EML tree equal to 0 for every real x?
- **Root existence:** does a given EML tree vanish at some real x?

## What is proved

The proof contains no `sorry`. Every theorem uses only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

| Theorem | Statement |
| --- | --- |
| `eml_zero_undecidable_final` | Richardson ⇒ "is t ≡ 0 on ℝ?" is not computable |
| `eml_root_undecidable_final` | Richardson ⇒ "does t have a real root?" is not computable |
| `compile_safe` | no compiled tree ever takes log 0, at any real input |
| `eml_zero_undecidable_partial`, `eml_root_undecidable_partial` | same results with log 0 left **undefined** |
| `eml_zero_undecidable_any`, `eml_root_undecidable_any` | same results with log 0 set to **any** value c |

The only hypothesis is Richardson's theorem itself, stated against an explicit Gödel
numbering of Richardson expressions (rationals, π, ln 2, x, +, ×, sin, exp, |·|).
The encodings, and the proof that the compiler is primitive recursive, are fully formalized.

## How it works

1. **Compiler.** Each Richardson primitive gets an EML *gadget*, a tree template proved
   correct for **every** real input, including 0 and negative numbers.
2. **Branch cuts.** Using the principal complex log is the delicate part. Arithmetic is done
   entirely in positive reals, for example a = eᵃ − (eᵃ − a). π and sin go through
   complex values whose imaginary parts are kept inside (−π, π].
3. **Absolute value without log 0.** |a| = a · sign(a). The sign is read off the branch cut:
   for u = 1 + i·g(a), where g(a) = 1/(1 + e⁻ᵃ) − ½ has the sign of a,
   the log gadget gives gL(−u) − log u = ∓iπ.
4. **Computability.** The compiler is primitive recursive (course-of-values recursion on
   Gödel numbers), so a decider for EML trees would yield a decider for Richardson
   expressions.

## Checking it

The proof builds against Mathlib (pinned in `lakefile.toml`). Every push is checked by GitHub Actions.

```bash
lake exe cache get
lake build
```

You can also paste `EmlRichardson.lean` into <https://live.lean-lang.org>.
