# SStructTT


| logic    | contraction | weakening |
| -------- | ----------- | --------- |
| linear   | no          | no        |
| affine   | no          | yes       |
| relevant | yes         | no        |
| unbound  | yes         | yes       |

If there are `Γ ⊢ m : A`, `A` is unbound and `B` is affine, can we weaken `Γ` with `B`?
```
Γ ⊢ m : A
-----------------
Γ, x : B ⊢ m : A


(λ(x : A). ⟨x, x⟩) m ~> ⟨m, m⟩
```

Contraction and weakening are connected in a subtle way. Consider some type
`A` without contraction but has weakening.

The following derivation is not admissible due to `A` lacking contraction:
```
Δ1 ⊢ m : X
-------------------(weaken)
Δ1, (x : A) ⊢ m : X

Δ2 ⊢ n : Y
-------------------(weaken)
Δ2, (x : A) ⊢ n : Y

Δ1, (x : A) ⊢ m : X         Δ2, (x : A) ⊢ n : Y
------------------------------------------------(tup)
Δ1, Δ2, (x : A) ⊢ ⟨m, n⟩ : X × Y
```

However, the conclusion is actually valid:
```
Δ1 ⊢ m : X         Δ2 ⊢ n : Y
------------------------------(tup)
Δ1, Δ2 ⊢ ⟨m, n⟩ : X × Y
----------------------------------(weaken)
Δ1, Δ2, (x : A) ⊢ ⟨m, n⟩ : X × Y
```

The `(x : A)` entry is *weak-contractible*.