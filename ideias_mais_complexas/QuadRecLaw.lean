import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factors -- Módulo onde o primeFactorsList está definido
import Mathlib.Tactic.NormNum.Prime -- Permite computações e provas numéricas rápidas
import Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD

open Nat

theorem impar_de_mdc {a p : Nat} (ha : Nat.gcd a (2 * p) = 1) : a % 2 = 1 := by
  by_contra h
  have h2a : 2 ∣  a := by omega
  have h2p : 2 ∣ (2*p) := dvd_mul_right 2 p
  have h2 : 2 ∣ Nat.gcd a (2*p) := Nat.dvd_gcd h2a (h2p)
  rw[ha] at h2 -- h2: 2|1
  rw[Nat.dvd_one] at h2 -- h2: 2=1
  simp at h2  -- h2 vira False, e a prova termina

theorem nao_div_de_mdc {a p : Nat} [hp_primo : Fact p.Prime] (ha : Nat.gcd a (2*p) = 1) : (a : ZMod p) ≠ 0 := by
  by_contra h
  -- intro h intro e by_contra fazem a mesma coisa
  rw[ZMod.natCast_eq_zero_iff] at h
  have hp2 : p ∣ (p * 2) := Nat.dvd_mul_right p 2
  have hp : p ∣ Nat.gcd a (p * 2) := Nat.dvd_gcd h (hp2)
  have hc :  2 * p = p * 2 := Nat.mul_comm 2 p
  rw[hc] at ha
  rw[ha] at hp
  have hprimo : p.Prime := hp_primo.out
  have h1 : 1 < p := Nat.Prime.one_lt hprimo
  rw [Nat.dvd_one] at hp     -- hp : p = 1
  simp[hp] at h1

  -- rw [hp] at hprimo          -- hprimo : Nat.Prime 1
  -- norm_num at hprimo

theorem ne_dois_de_impar {p : Nat} (hp : Odd p) : p ≠ 2 := by
  by_contra hp
  obtain ⟨k , hk⟩ := hp
  revert hp
  decide

lemma mesmo_conjunto {p : ℕ} (hp : Odd p) : Finset.Icc 1 ((p - 1) / 2) = Finset.Ico 1 (p / 2).succ := by
  obtain ⟨k, rfl⟩ := hp                 -- troca p por 2 * k + 1 em todo lugar
  ext j                                 -- ext j reduz a igualdade de conjuntos a “$j$ está no primeiro se e só se está no segundo”. Ou seja, dois conjuntos são iguais se têm os mesmos elementos--
  simp only [Finset.mem_Icc]
  simp only [Finset.mem_Ico]
  simp only [Nat.succ_eq_add_one]
  omega

theorem lema_gauss_nat (a p : ℕ) [h_primo : Fact p.Prime] (hp : Odd p) (ha : Nat.gcd a (2 * p) = 1) :
  legendreSym p a = (-1) ^ (∑ j ∈ Finset.Icc 1 ((p - 1) / 2), j * a / p) := by
   rw [mesmo_conjunto hp]
   exact ZMod.eisenstein_lemma (ne_dois_de_impar hp) (impar_de_mdc ha) (nao_div_de_mdc ha)

-- O teorema soma_qp é o que afirma que os pontos no interior do triângulo ΔACD somado com os pontos no interior do triângulo ΔABC é igual a ((p - 1) / 2) * ((q - 1) / 2).

-- theorem sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : Fact p.Prime] (hq0 : (q : ZMod p) ≠ 0) : ∑ a ∈ Ico 1 (p / 2).succ, a * q / p + ∑ a ∈ Ico 1 (q / 2).succ, a * p / q = p / 2 * (q / 2)

-- A prova de soma_qp consiste, essencialmente, em confirmar no Lean que temos as hipóteses

theorem soma_qp (p q : ℕ) [hp_primo : Fact p.Prime] [hq_primo : Fact q.Prime] (hp : Odd p) (hq : Odd q) (hpq : p ≠ q) :
    (∑ j ∈ Finset.Icc 1 ((p - 1) / 2), j * q / p) + (∑ k ∈ Finset.Icc 1 ((q - 1) / 2), k * p / q) = ((p - 1) / 2) * ((q - 1) / 2) := by
  -- Passo 1: trocar os conjuntos de índices
  rw [mesmo_conjunto hp, mesmo_conjunto hq]
  -- Passo 2: (p-1)/2 = p/2 e (q-1)/2 = q/2, pois p e q são ímpares
  have h1 : (p - 1) / 2 = p / 2 := by
    obtain ⟨k, rfl⟩ := hp
    omega
  have h2 : (q - 1) / 2 = q / 2 := by
    obtain ⟨k, rfl⟩ := hq
    omega
  rw [h1, h2]
  -- Passo 3: p não divide q
  have hq0 : (q : ZMod p) ≠ 0 := by
    by_contra h
    --intro h
    rw [ZMod.natCast_eq_zero_iff] at h          -- h : p ∣ q
    have hq_pr : q.Prime := hq_primo.out
    have hp_pr : p.Prime := hp_primo.out
    have h1p : 1 < p := Nat.Prime.one_lt hp_pr
    rcases Nat.Prime.eq_one_or_self_of_dvd hq_pr p h with h3 | h3
    · omega     -- caso p = 1: contradiz 1 < p
    · omega     -- caso p = q: contradiz p ≠ q
  -- Agora o objetivo é exatamente o enunciado de Mathlib
  apply ZMod.sum_mul_div_add_sum_mul_div_eq_mul
  exact hq0

--LEI DE RECIPROCIDADE QUADRATICA
theorem rec_quad (p q : ℕ) [hp_primo : Fact p.Prime] [hq_primo : Fact q.Prime] (hp : Odd p) (hq : Odd q) (hpq : p ≠ q) : (legendreSym p q) * (legendreSym q p) = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have h_mdc_um_q2p : Nat.gcd q (2 * p) = 1 := by -- Afirmação: mdc(q, 2p)=1
    rw [← Nat.coprime_iff_gcd_eq_one]
    have hq_pr : q.Prime := hq_primo.out
    have hp_pr : p.Prime := hp_primo.out
    have h2 : Nat.Coprime q 2 := by
      rw [Nat.Prime.coprime_iff_not_dvd hq_pr]  -- objetivo: ¬ q ∣ 2
      intro h                                   -- h : q ∣ 2
      have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have h1 : 1 < q := Nat.Prime.one_lt hq_pr
      rw [Nat.odd_iff] at hq                    -- hq : q % 2 = 1
      omega
    have hqp : Nat.Coprime q p := (Nat.coprime_primes hq_pr hp_pr).mpr hpq.symm
    exact Nat.Coprime.mul_right h2 hqp
  have h_mdc_um_p2q : Nat.gcd p (2 * q) = 1 := by -- Afirmação: mdc(p, 2q)=1
    rw [← Nat.coprime_iff_gcd_eq_one]
    have hq_pr : q.Prime := hq_primo.out
    have hp_pr : p.Prime := hp_primo.out
    have h2 : Nat.Coprime p 2 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp_pr]  -- objetivo: ¬ p ∣ 2
      intro h                                   -- h : p ∣ 2
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have h1 : 1 < p := Nat.Prime.one_lt hp_pr
      rw [Nat.odd_iff] at hp                    -- hq : p % 2 = 1
      omega
    have hpq : Nat.Coprime p q := (Nat.coprime_primes hp_pr hq_pr).mpr hpq -- .symm
    exact Nat.Coprime.mul_right h2 hpq

  rw [lema_gauss_nat q p hp h_mdc_um_q2p]
  rw [lema_gauss_nat p q hq h_mdc_um_p2q]
  rw [← pow_add]
  rw [soma_qp p q hp hq hpq]
