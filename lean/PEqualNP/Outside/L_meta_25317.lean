import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25317
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [1, 0]⟩,
    ⟨.or, [2, 0]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [5, 2]⟩,
    ⟨.and, [9, 6]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.not, [12]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [14, 11]⟩], 15⟩

end PEqualNP.Outside.L_meta_25317

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25317 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165564 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25317.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_25317.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
