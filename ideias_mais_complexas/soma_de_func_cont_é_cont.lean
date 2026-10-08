--import Mathlib.Topology.Continuous
--import Mathlib.Tactic.FunProp
--import Mathlib.Topology.MetricSpace.Basic
--import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
open Real


theorem continuousAt_add (f g : ℝ → ℝ) (a : ℝ) (hf : ContinuousAt f a) (hg : ContinuousAt g a) : ContinuousAt (fun x => f x + g x) a := by
  rw [Metric.continuousAt_iff] at *
  --at *, significa aplicar (rw[----]) tanto no seu Goal (o objetivo) quanto em todas as hipóteses listadas naquele momento.
  --Metric.continuousAt_iff : ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε
  --Este teorema foi aplicado nas hipóteses hf e hg. Assim, essas hipóteses acabam sendo reescritas como:  
            -- hf : ∀ ε > 0, ∃ δ > 0, ∀ x, dist x a < δ → dist (f x) (f a) < ε
            -- hg : ∀ ε > 0, ∃ δ > 0, ∀ x, dist x a < δ → dist (g x) (g a) < ε
  intro ε hε --intro é a tática para introduzir a hipóteses hε : ε>0 
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε/2) (half_pos hε)   -- continuidade de f --half_pos hε: ε>0 → ε/2>0
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε/2) (half_pos hε)   -- continuidade de g
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩ -- δ = min(δ₁, δ₂)
  have hx₁ : dist x a < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : dist x a < δ₂ := lt_of_lt_of_le hx (min_le_right _ _)

--Temos que introduzir um par de lemas auxiliares para evitar problema no passo (*) embaixo
 
  have h_dist1 : dist (f x + g x) (f a + g x) = dist (f x) (f a) := by
    rw [Real.dist_eq, Real.dist_eq]
    congr 1 -- troca de objetivo: No lugar de mostrar |f x + g x - (f a + g x)| = |f x - f a| podemos trocar por f x + g x - (f a + g x) = f x - f a (sem valor absoluto!)
    ring
/-
--congr (abreviação de congruence) é uma tática que serve para reduzir uma meta de igualdade entre duas expressões complexas à igualdade de suas partes componentes. Em termos simples, para (f(x) = f(y)), a tática congr assume que a f é a mesma dos dois lados e transforma o seu objetivo em provar apenas que x = y. Ela funciona para qualquer função \[f\], mesmo que você não saiba se ela é injetiva ou não no sentido estrito.
-/
  have h_dist2 : dist (f a + g x) (f a + g a) = dist (g x) (g a) := by
    rw [Real.dist_eq, Real.dist_eq]
    congr 1
    ring
  calc
    dist (f x + g x) (f a + g a)
      ≤ dist (f x + g x) (f a + g x) + dist (f a + g x) (f a + g a) := dist_triangle _ _ _
    _ =   dist (f x) (f a) + dist (g x) (g a)                       := by rw [h_dist1 , h_dist2]--(*)
    _ < ε / 2 + ε / 2                                               := add_lt_add (h₁ hx₁) (h₂ hx₂)
    _ = ε   := add_halves ε
  /--/
O que acontece na linha 19?:

  após a linha 13, o seu Goal era provar uma existência adivinhando o δ da soma (⊢ ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x + g x) (f a + g a) < ε)

  Esse objetivo tem exatamente três partes escondidas dentro dos conectivos e do ∃ : 
    1- O valor do δ que serve para a soma.
    2- A prova de que δ>0.
    3- A prova de "para todo x, a distância menor que δ implica na distância menor que ε. 
    
    o que refine faz com cada uma dessas três partes: 
     1- min δ₁ δ₂  "O δ que resolve o problema da soma é o mínimo entre o δ_1 e δ_2". Nesse caso, Lean aceita e substitui o ∃ δ por esse valor. 
     2- lt_min hδ₁ hδ₂ (A prova de que ele é positivo). O Lean precisa ter certeza de que esse mínimo é maior que zero. O teorema lt_min é a prova de que min δ₁ δ₂ > 0.
     3- fun x hx => ?_ (O miolo da prova) Aqui você está lidando com o pedaço ∀ {x}, dist x a < δ → .... O fun x hx introduz a variável x e assume a hipótese hx (esta hipótese é dist(x, a) < \min(δ_1 , δ_2)\)). O ?_ (chamado de placeholder ou goal nomeado) diz ao Lean: "Eu ainda não sei como provar que a distância da soma é menor que ε, então, crie um novo Goal para mim com isso!". 
