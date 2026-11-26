import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_20381
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.TopForm
private def advance (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def bit (b v : ℕ) := v.testBit b
private def packedStep (w : List ℕ) (g : Gate) : List ℕ :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  w ++ [if g.op matches .and then a &&& b else a ||| b]

private theorem mapD (w : List ℕ) (b k : ℕ) :
    (w.map (bit b)).getD k false = bit b (w.getD k 0) := by
  simpa [bit] using (List.getD_map (l:=w) (d:=0) (n:=k) (bit b))

private theorem packed_advance (g : Gate) (w : List ℕ) (b : ℕ)
    (op : g.op = GateOp.and ∨ g.op = GateOp.or) (len : g.inputs.length = 2) :
    (packedStep w g).map (bit b) = advance (w.map (bit b)) g := by
  cases g with
  | mk o ins =>
    change ins.length = 2 at len
    cases ins with
    | nil => simp at len
    | cons u rest =>
      cases rest with
      | nil => simp at len
      | cons v tail =>
        cases tail with
        | cons i t => simp at len
        | nil =>
          rcases op with op | op <;> change o = _ at op <;> subst o <;>
            simp [packedStep,advance,GateOp.eval,bit,List.getD_eq_getElem?_getD] <;> cases hu : w[u]? <;> cases hv : w[v]? <;> simp [bit]

private theorem sim (gs : List Gate) (good : ∀ g ∈ gs,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : List ℕ) (b : ℕ) :
    (gs.foldl packedStep w).map (bit b) = gs.foldl advance (w.map (bit b)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have h := good g (by simp)
    rw [List.foldl_cons,List.foldl_cons,ih (fun h hh => good h (by simp [hh])),
      packed_advance _ _ _ h.1 h.2]


private def inputs (i : Fin 8) : List ℕ :=
  List.ofFn (fun u : Fin 8 => if u=i then 255 else 0) ++ List.ofFn (fun v : Fin 8 => 2^v.val)

private theorem inputs_decode : ∀ i j : Fin 8, (inputs i).map (bit j.val) = oneEach i j := by
  decide +kernel

private def row (C : Circuit) (i : Fin 8) := (C.gates.foldl packedStep (inputs i)).getD C.output 0

private theorem pixel (C : Circuit) (legal : IsAO2 16 C) (i j : Fin 8) :
    C.eval (oneEach i j) = (row C i).testBit j.val := by
  change (C.gates.foldl advance (oneEach i j)).getD C.output false = _
  rw [← inputs_decode i j,← sim _ (fun g hg => ⟨legal.1 g hg,legal.2.2 g hg⟩),mapD]
  rfl

private theorem isMono (C : Circuit) (legal : IsAO2 16 C) : Monotone2 C := by
  intro g hg
  refine ⟨?_,?_⟩
  · simpa using legal.1 g hg
  · have := legal.2.2 g hg
    omega


def circ : Circuit := ⟨[
  ⟨.or,[0,13]⟩,
  ⟨.or,[3,15]⟩,
  ⟨.or,[4,6]⟩,
  ⟨.or,[1,14]⟩,
  ⟨.or,[2,9]⟩,
  ⟨.or,[18,11]⟩,
  ⟨.or,[10,21]⟩,
  ⟨.or,[5,8]⟩,
  ⟨.or,[6,14]⟩,
  ⟨.or,[4,7]⟩,
  ⟨.or,[21,12]⟩,
  ⟨.or,[26,19]⟩,
  ⟨.or,[5,24]⟩,
  ⟨.or,[25,16]⟩,
  ⟨.or,[29,19]⟩,
  ⟨.or,[20,12]⟩,
  ⟨.or,[7,31]⟩,
  ⟨.or,[10,17]⟩,
  ⟨.or,[28,33]⟩,
  ⟨.or,[1,20]⟩,
  ⟨.or,[35,17]⟩,
  ⟨.and,[30,23]⟩,
  ⟨.and,[32,34]⟩,
  ⟨.and,[16,27]⟩,
  ⟨.and,[36,22]⟩,
  ⟨.or,[37,38]⟩,
  ⟨.or,[41,39]⟩,
  ⟨.or,[42,40]⟩],43⟩
private theorem checked : IsAO2 16 circ := by decide +kernel
theorem basis : Monotone2 circ := isMono _ checked
private def rows : Array ℕ := #[89, 45, 204, 30, 163, 114, 178, 197]
private theorem checkedRows : ∀ i : Fin 8, row circ i = rows[i.val]?.getD 0 := by decide +kernel
theorem outputs : Represents (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) circ := by
  have bits : ∀ i j : Fin 8, (rows[i.val]?.getD 0).testBit j.val =
      (14245574616248233305 : ℕ).testBit (8 * i.val + j.val) := by decide +kernel
  intro i j
  rw [pixel _ checked,checkedRows]
  exact bits i j
end PEqualNP.Outside.L_meta_20381

theorem PEqualNP.Outside.L_meta_20381 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_20381.circ,PEqualNP.Outside.L_meta_20381.basis,by decide,PEqualNP.Outside.L_meta_20381.outputs⟩
