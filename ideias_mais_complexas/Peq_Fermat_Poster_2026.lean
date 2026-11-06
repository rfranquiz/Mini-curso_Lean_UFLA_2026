import Mathlib.Tactic.Linarith
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.ModEq

import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.Finite.Basic

open ZMod
open Nat

variable (p : ℕ) [Fact p.Prime]
--local notation "G" => (ZMod p)ˣ

-- O tipo do grupo de unidades (elementos invertíveis)
#check (ZMod p)ˣ


theorem PeqFermat (a : ℤ) {p : ℕ} (hp : p.Prime) : a ^ p ≡ a [ZMOD (p : ℤ  )] := by
  have : Fact p.Prime := ⟨hp⟩
  set G_grupo := (ZMod p)ˣ
  have Ord_G : Fintype.card G_grupo = p - 1 := by
    rw[ZMod.card_units]
  -- trocar a congruência em ℤ por uma igualdade em ZMod p
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  -- objetivo: (a : ZMod p) ^ p = (a : ZMod p)
  by_cases ha : (a : ZMod p) = 0
-- caso p ∣ a: os dois lados são 0
  · rw [ha]
    have hp_ne_zero {p : ℕ} (hp : p.Prime) : p ≠ 0 := Nat.Prime.ne_zero hp 
    rw[zero_pow (hp_ne_zero hp)]
--=============================================================================
-- caso p ∤ a: a define um elemento do grupo  
  · let u : (ZMod p)ˣ := Units.mk0 (a : ZMod p) ha
    have hu : (u : ZMod p) = a := rfl
    -- (i) k = ordem de u, e u ^ k = 1
    set k := orderOf u with hk
    have huk : u ^ k = 1 := pow_orderOf_eq_one u
    -- a mesma coisa em ZMod p: a ^ k = 1
    have hak : (a : ZMod p) ^ k = 1 := by
      rw [← hu]
      rw[← Units.val_pow_eq_pow_val]
      rw[huk]
      rw[Units.val_one]
    -- (ii) H = subgrupo gerado por u, e |H| = k
    let H : Subgroup (ZMod p)ˣ := Subgroup.zpowers u
    have hH : Nat.card H = k := Nat.card_zpowers u
    -- (iii) Lagrange: |H| divide |G|
    have hLag : Nat.card H ∣ Nat.card (ZMod p)ˣ := Subgroup.card_subgroup_dvd_card H
    -- (iv) logo k divide p - 1
    have hk_dvd : k ∣ p - 1 := by
      rw [← hH]
      rw[← Ord_G]
      rw[← Nat.card_eq_fintype_card]
      exact hLag
    -- (v) escrevendo p - 1 = k * m, temos a ^ (p - 1) = (a ^ k) ^ m = 1
    obtain ⟨m, hm⟩ := hk_dvd
    have h2 : (a : ZMod p) ^ (p - 1) = 1 := by
      rw [hm, pow_mul, hak, one_pow]
    -- (vi) a ^ p = a ^ (p - 1) * a = a
    calc (a : ZMod p) ^ p = (a : ZMod p) ^ (p - 1) * a := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
      _ = a := by rw [h2, one_mul]
