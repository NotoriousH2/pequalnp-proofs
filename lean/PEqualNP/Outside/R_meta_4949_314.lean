import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One pair of positive flag supports per OR. A free AND may inherit the
-- negative witness from any child whose positive support contains its own.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4949_314
    (compile : let E := Fin 4 × Fin 13
    let step := fun (Z : Finset E → Prop) (q : Finset E × Finset E) (s : Finset E) =>
      Z s ∨ (Z q.1 ∧ Z q.2 ∧ s ⊆ q.1 ∪ q.2)
    ∀ (P : E → Fin 26 → Bool) (C : Circuit), Monotone2 C →
    (∀ e, circuitFun 26 C (P e)=true) →
    ∃ Q : List (Finset E × Finset E), Q.length =
      {j : Fin C.gates.length | (C.gates.get j).op=GateOp.or}.ncard ∧
      ∀ x : Fin 26 → Bool, circuitFun 26 C x=false →
      let Z := fun s : Finset E => s=∅ ∨ ∃ i : Fin 26, x i=false ∧ ∀ e ∈ s, P e i=true
      Q.foldl step Z Finset.univ)
    (exclude : let E := Fin 4 × Fin 13
    let step := fun (Z : Finset E → Prop) (q : Finset E × Finset E) (s : Finset E) =>
      Z s ∨ (Z q.1 ∧ Z q.2 ∧ s ⊆ q.1 ∪ q.2)
    let P := fun (e : E) (i : Fin 26) =>
      let p := e.2 + ([0,1,3,9] : List (Fin 13)).getD e.1.val 0
      decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 e.2)
    ∀ (I : List (Finset E × Finset E)) (T : Finset (Finset E)),
      (∀ q ∈ I, q.1 ∪ q.2 ≠ Finset.univ) → (∀ (r : Fin 36) (k : Fin 13),
      let m := ((1259886254397126488781191988044141515605159741757169136265957107063160921435871760439256437543488169396155399 : ℕ) >>> (10*r.val)) % 1024
      let X := Finset.univ.filter fun p : Fin 13 => m.testBit (p-k).val
      let x := fun (i : Fin 26) => decide ((∃ p ∈ X, i=Fin.castAdd 13 p) ∨
        ∃ l : Fin 13, i=Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬(p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9))
      let Z := fun s : Finset E => s=∅ ∨ ∃ i : Fin 26, x i=false ∧ ∀ e ∈ s, P e i=true
      let D := I.foldl step Z
      D Finset.univ ∨ ∃ a ∈ T, D a ∧ D aᶜ) → 51 ≤ I.length + T.card) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) →       (∀ (x4 : ℕ) (x5 : Fin (13 : ℕ)),           (x4 ∈               have x6 : List ℕ :=                 have x6 : List ℕ :=                   have x6 : List ℕ := [(281 : ℕ), (297 : ℕ), (329 : ℕ), (337 : ℕ), (549 : ℕ)];                   (201 : ℕ) :: (265 : ℕ) :: (273 : ℕ) :: (275 : ℕ) :: x6;                 have x7 : List ℕ := (133 : ℕ) :: (135 : ℕ) :: (137 : ℕ) :: (141 : ℕ) :: (195 : ℕ) :: x6;                 (97 : ℕ) :: (101 : ℕ) :: (105 : ℕ) :: (131 : ℕ) :: x7;               have x7 : List ℕ :=                 have x7 : List ℕ := (73 : ℕ) :: (77 : ℕ) :: (81 : ℕ) :: (83 : ℕ) :: (85 : ℕ) :: x6;                 (41 : ℕ) :: (67 : ℕ) :: (69 : ℕ) :: (71 : ℕ) :: x7;               have x8 : List ℕ := (25 : ℕ) :: (29 : ℕ) :: (35 : ℕ) :: (37 : ℕ) :: (39 : ℕ) :: x7;               (7 : ℕ) :: (13 : ℕ) :: (19 : ℕ) :: (21 : ℕ) :: x8) →             have x7 : Finset (Fin (13 : ℕ)) := {x7 : Fin (13 : ℕ) | x4.testBit ↑(x7 - x5) = Bool.true};             (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ ∀ x10 ∈ x7, ¬(x10 = x9 ∨ x10 = x9 + (1 : Fin (13 : ℕ)) ∨ x10 = x9 + (3 : Fin (13 : ℕ)) ∨ x10 = x9 + (9 : Fin (13 : ℕ))))) = Bool.false) →         (51 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  intro C hm hp hn
  let E := Fin 4 × Fin 13
  let P := fun (e : E) (i : Fin 26) =>
      let p := e.2 + ([0,1,3,9] : List (Fin 13)).getD e.1.val 0
      decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 e.2)
  have accepts : ∀ e : E, circuitFun 26 C (P e) = true := by
    have h : ∀ e : Fin 4 × Fin 13,
        let p := e.2 + ([0,1,3,9] : List (Fin 13)).getD e.1.val 0
        p=e.2 ∨ p=e.2+1 ∨ p=e.2+3 ∨ p=e.2+9 := by decide +kernel
    exact fun e => hp _ e.2 (h e)
  obtain ⟨Q, size, reject⟩ := compile P C hm accepts
  let Mask := Finset E
  let step := fun (Z : Mask → Prop) (q : Mask × Mask) (s : Mask) =>
    Z s ∨ (Z q.1 ∧ Z q.2 ∧ s ⊆ q.1 ∪ q.2)
  let down := fun (Z : Mask → Prop) => ∀ a b, a ⊆ b → Z b → Z a
  have downFold (I : List (Mask × Mask)) (Z : Mask → Prop) (hz : down Z) :
      down (I.foldl step Z) := by
    induction I generalizing Z with
    | nil => exact hz
    | cons q I ih =>
      apply ih
      intro a b sub hb
      rcases hb with h|⟨u,v,w⟩
      · exact Or.inl (hz _ _ sub h)
      · exact Or.inr ⟨u,v,sub.trans w⟩
  have pack (V : List (Mask × Mask)) :
      ∃ (I : List (Mask × Mask)) (T : Finset Mask),
        I.length + T.card ≤ V.length ∧ (∀ q ∈ I, q.1 ∪ q.2 ≠ Finset.univ) ∧
        ∀ (Z : Mask → Prop), down Z → ∀ s, V.foldl step Z s →
          I.foldl step Z s ∨ ∃ a ∈ T, I.foldl step Z a ∧ I.foldl step Z aᶜ := by
    induction V using List.reverseRecOn with
    | nil => exact ⟨[],∅,by simp,by simp,fun _ _ _ h => Or.inl h⟩
    | append_singleton V q ih =>
      obtain ⟨I,T,sz,proper,old⟩ := ih
      by_cases top : q.1 ∪ q.2 = Finset.univ
      · refine ⟨I,insert q.1 T,?_,proper,?_⟩
        · have := Finset.card_insert_le q.1 T
          simp only [List.length_append,List.length_singleton]; omega
        intro Z hz s hs
        have liftOld {a : Mask} (ha : a ∈ T) : a ∈ insert q.1 T := Finset.mem_insert_of_mem ha
        simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] at hs
        rcases hs with h|⟨h1,h2,_⟩
        · rcases old Z hz s h with yes|⟨a,ha,hit⟩
          · exact Or.inl yes
          · exact Or.inr ⟨a,liftOld ha,hit⟩
        · rcases old Z hz _ h1 with a1|⟨a,ha,hit⟩
          · rcases old Z hz _ h2 with a2|⟨a,ha,hit⟩
            · have sub : q.1ᶜ ⊆ q.2 := by
                intro p hp
                have mem : p ∈ q.1 ∪ q.2 := top ▸ Finset.mem_univ p
                exact (Finset.mem_union.mp mem).resolve_left (Finset.mem_compl.mp hp)
              exact Or.inr ⟨q.1,Finset.mem_insert_self _ _,a1,downFold I Z hz _ _ sub a2⟩
            · exact Or.inr ⟨a,liftOld ha,hit⟩
          · exact Or.inr ⟨a,liftOld ha,hit⟩
      · refine ⟨I++[q],T,by simp only [List.length_append,List.length_singleton]; omega,?_,?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with h|h
          · exact proper p h
          · obtain rfl : p = q := List.mem_singleton.mp h
            exact top
        intro Z hz s hs
        simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] at hs ⊢
        have liftTip (tip : ∃ a ∈ T, I.foldl step Z a ∧ I.foldl step Z aᶜ) :
            ∃ a ∈ T, step (I.foldl step Z) q a ∧ step (I.foldl step Z) q aᶜ := by
          obtain ⟨a,ha,b,c⟩ := tip
          exact ⟨a,ha,Or.inl b,Or.inl c⟩
        rcases hs with h|⟨h1,h2,sub⟩
        · rcases old Z hz s h with yes|tip
          · exact Or.inl (Or.inl yes)
          · exact Or.inr (liftTip tip)
        · rcases old Z hz _ h1 with a1|tip
          · rcases old Z hz _ h2 with a2|tip
            · exact Or.inl (Or.inr ⟨a1,a2,sub⟩)
            · exact Or.inr (liftTip tip)
          · exact Or.inr (liftTip tip)
  obtain ⟨I,T,sz,proper,sim⟩ := pack Q
  rw [←size]
  apply Nat.le_trans (exclude I T proper ?_) sz
  intro r k
  let m := ((1259886254397126488781191988044141515605159741757169136265957107063160921435871760439256437543488169396155399 : ℕ) >>> (10*r.val)) % 1024
  let X := Finset.univ.filter fun p : Fin 13 => m.testBit (p-k).val
  let x := fun (i : Fin 26) => decide ((∃ p ∈ X, i=Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, i=Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬(p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9))
  refine sim _ ?_ Finset.univ ?_
  · intro a b sub hb
    rcases hb with rfl|⟨i,hi,all⟩
    · exact Or.inl (Finset.subset_empty.mp sub)
    · exact Or.inr ⟨i,hi,fun e he => all e (sub he)⟩
  apply reject x
  let masks : List ℕ := [7,13,19,21,25,29,35,37,39,41,67,69,71,73,77,81,83,85,97,101,105,131,133,135,137,141,195,201,265,273,275,281,297,329,337,549]
  have inside : ∀ j : Fin 36, ((1259886254397126488781191988044141515605159741757169136265957107063160921435871760439256437543488169396155399 : ℕ) >>> (10*j.val)) % 1024 ∈ masks := by decide +kernel
  exact hn m k (inside r)

