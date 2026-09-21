import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace UnimodularGravity

abbrev Index4 := Fin 4
abbrev Tensor4 := Index4 → Index4 → ℝ

def tensor_add (A B : Tensor4) : Tensor4 := fun μ ν => A μ ν + B μ ν
def tensor_sub (A B : Tensor4) : Tensor4 := fun μ ν => A μ ν - B μ ν
def tensor_smul (c : ℝ) (A : Tensor4) : Tensor4 := fun μ ν => c * A μ ν

def tensor_mul (A B : Tensor4) : Tensor4 :=
  fun μ ν => A μ 0 * B 0 ν + A μ 1 * B 1 ν + A μ 2 * B 2 ν + A μ 3 * B 3 ν

def tensor_trace (M : Tensor4) : ℝ :=
  M 0 0 + M 1 1 + M 2 2 + M 3 3

structure Metric4 where
  g : Tensor4
  inv_g : Tensor4
  inv_mul_cancel : tensor_mul inv_g g = fun μ ν => if μ = ν then 1 else 0

noncomputable def metric_trace (m : Metric4) (T : Tensor4) : ℝ :=
  tensor_trace (tensor_mul m.inv_g T)

noncomputable def trace_free_projection (m : Metric4) (T : Tensor4) : Tensor4 :=
  tensor_sub T (tensor_smul ((1 / 4) * metric_trace m T) m.g)

def T_loop (m : Metric4) (ρ_loop : ℝ) : Tensor4 :=
  tensor_smul (-ρ_loop) m.g

lemma trace_identity :
    tensor_trace (fun μ ν => if μ = ν then (1 : ℝ) else 0) = 4 := by
  unfold tensor_trace
  dsimp
  ring

lemma tensor_mul_loop (m : Metric4) (ρ_loop : ℝ) :
    tensor_mul m.inv_g (T_loop m ρ_loop) =
      tensor_smul (-ρ_loop) (fun μ ν => if μ = ν then 1 else 0) := by
  unfold tensor_mul T_loop tensor_smul
  ext μ ν
  have h_inv := congr_fun (congr_fun m.inv_mul_cancel μ) ν
  unfold tensor_mul at h_inv
  linear_combination -ρ_loop * h_inv

theorem metric_trace_T_loop (m : Metric4) (ρ_loop : ℝ) :
    metric_trace m (T_loop m ρ_loop) = -4 * ρ_loop := by
  unfold metric_trace
  rw [tensor_mul_loop m ρ_loop]
  unfold tensor_trace tensor_smul
  dsimp
  ring

theorem unimodular_trace_free_loop_decoupling (m : Metric4) (ρ_loop : ℝ) :
    trace_free_projection m (T_loop m ρ_loop) = fun _ _ => 0 := by
  ext μ ν
  unfold trace_free_projection tensor_sub
  rw [metric_trace_T_loop m ρ_loop]
  unfold T_loop tensor_smul
  ring

theorem unimodular_decoupling_component (m : Metric4) (ρ_loop : ℝ) (μ ν : Index4) :
    trace_free_projection m (T_loop m ρ_loop) μ ν = 0 := by
  have h := congr_fun (congr_fun (unimodular_trace_free_loop_decoupling m ρ_loop) μ) ν
  exact h

#print axioms metric_trace_T_loop
#print axioms unimodular_trace_free_loop_decoupling
#print axioms unimodular_decoupling_component

end UnimodularGravity
