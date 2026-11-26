import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25330
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.not, [4]⟩,
    ⟨.or, [2, 0]⟩,
    ⟨.and, [7, 1]⟩,
    ⟨.or, [7, 1]⟩,
    ⟨.and, [3, 2]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25330

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25330 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180765 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25330.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_25330.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
