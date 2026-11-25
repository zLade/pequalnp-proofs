import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13185_aux

abbrev W := BitVec 64

def want : W := 17215267586907368104

def initial : List W := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720]

def negatives : List ℕ := [0, 1, 2, 4, 6, 8, 10, 12, 16, 17, 18, 20, 24, 28, 32, 33, 34, 36, 38, 40, 42, 44, 48, 49, 50, 52, 56, 60]

def separates (p : Bool) (q : ℕ) (w : W) : W :=
  if w.getLsbD q then (if p then ~~~w else 0) else w

def cuts (p : Bool) (ws : List W) : Bool :=
  negatives.all fun q => (ws.foldr (fun w r => separates p q w ||| r) 0 &&& want) == want

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a::l => (a,l) :: (singles l).map (fun (b,r) => (b,a::r))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a::l => ((singles l).map (fun (b,r) => (a,b,r))) ++
      ((pairs l).map (fun (b,c,r) => (b,c,a::r)))

def fresh (z : W) (ws : List W) : Bool :=
  z != 0 && z != -1 && !ws.contains z

def step1 (k : ℕ) (next : Bool → List W → Bool) (a : W) (r : List W) : Bool :=
  let z := ~~~a
  fresh z (a::r) && (next true (z::r) || (r.length < k && next true (z::a::r)))

def step2 (k : ℕ) (p : Bool) (next : Bool → List W → Bool) (a b : W) (r : List W) : Bool :=
  [a &&& b, a ||| b].any fun z =>
    fresh z (a::b::r) &&
      (next p (z::r) ||
        (r.length < k && (next p (z::a::r) || next p (z::b::r))) ||
        (r.length + 1 < k && next p (z::a::b::r)))

def explore : ℕ → Bool → List W → Bool
  | 0, _, ws => ws == [want]
  | k+1, p, ws => ws == [want] ||
      (decide (ws.length ≤ k+2) && cuts p ws &&
        ((p && decide (ws.length ≤ k+1) && (singles ws).any (fun (a,r) => step1 k (explore k) a r)) ||
          (pairs ws).any (fun (a,b,r) => step2 k p (explore k) a b r)))

def Move (p : Bool) (xs : List W) (z : W) (q : Bool) : Prop :=
  z ≠ 0 ∧ z ≠ -1 ∧
    ((∃ a b, xs = [a,b] ∧ a ≠ b ∧ (z = a &&& b ∨ z = a ||| b) ∧ q = p) ∨
     (∃ a, xs = [a] ∧ z = ~~~a ∧ p = true ∧ q = true))

def Build : ℕ → Bool → Finset W → Prop
  | 0, _, s => want ∈ s
  | k+1, p, s => Build k p s ∨ ∃ xs z q, Move p xs z q ∧ xs.toFinset ⊆ s ∧ Build k q (insert z s)

def Live : ℕ → Bool → Finset W → Prop
  | 0, _, s => s = {want}
  | k+1, p, s => Live k p s ∨ ∃ xs z q r, Move p xs z q ∧ z ∉ s ∧
      s = xs.toFinset ∪ r ∧ Live k q (insert z r)


theorem live_allow {k : ℕ} {t : Finset W} (h : Live k false t) : Live k true t := by
  induction k generalizing t with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨ys,w,b,r,mv,hw,eq,hr⟩
    · exact Or.inl (ih skip)
    · rcases mv with ⟨n0,n1,⟨a,c,hs,ha,hoz,rfl⟩ | ⟨a,_,_,bad,_⟩⟩
      · exact Or.inr ⟨ys,w,true,r,⟨n0,n1,Or.inl ⟨a,c,hs,ha,hoz,rfl⟩⟩,hw,eq,ih hr⟩
      · contradiction

theorem build_live {k p s} (h : Build k p s) : ∃ t ⊆ s, Live k p t := by
  induction k generalizing p s with
  | zero => exact ⟨{want},Finset.singleton_subset_iff.mpr h,rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨xs,z,q,mv,hops,tail⟩
    · obtain ⟨t,ht,htl⟩ := ih skip
      exact ⟨t,ht,Or.inl htl⟩
    obtain ⟨t,ht,hl⟩ := ih tail
    by_cases sub : t ⊆ s
    · rcases mv.2.2 with ⟨a,b,_,_,_,hqp⟩ | ⟨a,_,_,hp,hq⟩
      · exact ⟨t,sub,Or.inl (hqp ▸ hl)⟩
      · exact ⟨t,sub,Or.inl (by simpa [hp,hq] using hl)⟩
    have hz : z ∈ t := by
      by_contra nh
      apply sub
      intro w hw
      exact (Finset.mem_insert.mp (ht hw)).resolve_left (fun e => nh (e ▸ hw))
    have fresh : z ∉ s := fun hm => sub ((Finset.insert_eq_of_mem hm) ▸ ht)
    let r := t.erase z
    have rsub : r ⊆ s := by
      intro w hw
      exact (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hw).2)).resolve_left
        (Finset.mem_erase.mp hw).1
    have both : xs.toFinset ∪ r ⊆ s := Finset.union_subset hops rsub
    exact ⟨_,both,Or.inr ⟨xs,z,q,r,mv,fun hm => fresh (both hm),rfl,by simpa [r,Finset.insert_erase hz] using hl⟩⟩

theorem live_card {k p s} (h : Live k p s) : s.card ≤ k+1 := by
  induction k generalizing p s with
  | zero => change s = {want} at h; simp [h]
  | succ k ih =>
    rcases h with h | ⟨xs,z,q,r,mv,hz,rfl,tail⟩
    · exact (ih h).trans (by omega)
    · have rz : z ∉ r := fun hz' => hz (Finset.mem_union_right _ hz')
      have hc := ih tail
      rw [Finset.card_insert_of_notMem rz] at hc
      have hl : xs.length ≤ 2 := by
        rcases mv.2.2 with ⟨a,b,rfl,_,_,_⟩ | ⟨a,rfl,_,_,_⟩ <;> simp
      have hu := Finset.card_union_le xs.toFinset r
      have hx := List.toFinset_card_le xs
      omega

theorem live_first {k p s} (h : Live (k+1) p s) :
    s = {want} ∨ ∃ xs z q r, Move p xs z q ∧ z ∉ s ∧
      s = xs.toFinset ∪ r ∧ Live k q (insert z r) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with h | h
    · rcases ih h with h | ⟨xs,z,q,r,mv,fresh,hs,more⟩
      · exact Or.inl h
      · exact Or.inr ⟨xs,z,q,r,mv,fresh,hs,Or.inl more⟩
    · exact Or.inr h

def sep (p : Bool) (r q : ℕ) (w : W) : Prop :=
  (w.getLsbD r = true ∧ w.getLsbD q = false) ∨
    (p = true ∧ w.getLsbD r = false ∧ w.getLsbD q = true)

theorem preserves_sep {k p s} (h : Live k p s) (r q : ℕ)
    (pr : want.getLsbD r = true) (nq : want.getLsbD q = false)
    (hr : r < 64) (hq : q < 64) : ∃ w ∈ s, sep p r q w := by
  induction k generalizing p s with
  | zero =>
    change s = {want} at h
    exact ⟨want,by simp [h],Or.inl ⟨pr,nq⟩⟩
  | succ k ih =>
    rcases h with h | ⟨xs,z,b,t,mv,hz,rfl,tail⟩
    · exact ih h
    obtain ⟨w,hw,hs⟩ := ih tail
    rcases Finset.mem_insert.mp hw with rfl | hmem
    · rcases mv.2.2 with ⟨a,c,rfl,_,hop,rfl⟩ | ⟨a,rfl,rfl,rfl,rfl⟩
      · have hh : sep b r q a ∨ sep b r q c := by
          rcases hop with rfl | rfl <;> unfold sep at * <;>
            simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,Bool.and_eq_true,Bool.or_eq_true,
              Bool.and_eq_false_iff,Bool.or_eq_false_iff] at * <;> tauto
        exact hh.elim (fun h => ⟨a,by simp,h⟩) (fun h => ⟨c,by simp,h⟩)
      · rcases hs with ⟨hp,hq'⟩ | ⟨_,hp,hq'⟩
        · exact ⟨a,by simp,Or.inr ⟨rfl,by simpa [BitVec.getLsbD_not,hr] using hp,by simpa [BitVec.getLsbD_not,hq] using hq'⟩⟩
        · exact ⟨a,by simp,Or.inl ⟨by simpa [BitVec.getLsbD_not,hr] using hp,by simpa [BitVec.getLsbD_not,hq] using hq'⟩⟩
    · refine ⟨w,Finset.mem_union_right _ hmem,?_⟩
      rcases mv.2.2 with ⟨a,c,_,_,_,rfl⟩ | ⟨a,_,_,rfl,rfl⟩
      · exact hs
      · exact hs

theorem all_cuts {k p} {ws : List W} (h : Live k p ws.toFinset) :
    cuts p ws = true := by
  apply List.all_eq_true.mpr
  intro q qmem
  have hq : q < 64 := by
    have ok : ∀ x ∈ negatives, x < 64 := by decide +kernel
    exact ok q qmem
  have nq : want.getLsbD q = false := by
    have ok : ∀ x ∈ negatives, want.getLsbD x = false := by decide +kernel
    exact ok q qmem
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  cases eq : want.getLsbD i
  · simp
  · simp only [Bool.and_true]
    obtain ⟨w,hw,sepW⟩ := preserves_sep h i q eq nq hi hq
    have valid : (separates p q w).getLsbD i = true := by
      rcases sepW with ⟨a,b⟩ | ⟨rfl,a,b⟩
      · simp [separates,a,b]
      · simpa [separates,b,hi,BitVec.getLsbD_eq_getElem hi] using a
    have fold : ∀ (ws' : List W), w ∈ ws' →
        (ws'.foldr (fun v r => separates p q v ||| r) 0).getLsbD i = true := by
      intro ws'
      induction ws' with
      | nil => simp
      | cons a l ih =>
        intro hm
        rcases List.mem_cons.mp hm with rfl | inTail
        · simp [BitVec.getLsbD_or,valid]
        · rw [List.foldr_cons,BitVec.getLsbD_or,Bool.or_eq_true]; exact Or.inr (ih inTail)
    exact fold ws (List.mem_toFinset.mp hw)

open PEqualNP.CircuitLowerBounds

def gateWord (ws : List W) (g : Gate) : W :=
  let args := g.inputs.map fun i => ws.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes _)
  | .or => args.foldr (· ||| ·) 0
  | .not => ~~~(args.headD 0)
  | _ => 0

def stepWord (ws : List W) (g : Gate) : List W := ws ++ [gateWord ws g]
def stepBool (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def GateOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem getD_bits (ws : List W) (r j : Nat) :
    (ws.map fun w => w.getLsbD r).getD j false = (ws.getD j 0).getLsbD r := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> simp

theorem fold_and_bit (ws : List W) (r : Fin 64) :
    (ws.foldr (· &&& ·) (BitVec.allOnes _)).getLsbD r.val =
      (ws.map fun w => w.getLsbD r.val).all id := by
  induction ws with
  | nil => simp only [List.foldr_nil,List.map_nil,List.all_nil,BitVec.getLsbD_allOnes,r.isLt,decide_true]
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.all_cons, BitVec.getLsbD_and, id, ih]

theorem fold_or_bit (ws : List W) (r : Fin 64) :
    (ws.foldr (· ||| ·) 0).getLsbD r.val =
      (ws.map fun w => w.getLsbD r.val).any id := by
  induction ws with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.any_cons, BitVec.getLsbD_or, id, ih]

theorem step_bits (ws : List W) (g : Gate) (hg : GateOK g) (r : Fin 64) :
    (stepWord ws g).map (fun w => w.getLsbD r.val) =
      stepBool (ws.map fun w => w.getLsbD r.val) g := by
  have hopen := hg.1
  unfold stepWord stepBool
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
  unfold gateWord
  rcases hopen with h | h | h
  · simp only [h, GateOp.eval, fold_and_bit, List.map_map, Function.comp_def, getD_bits]
  · simp only [h, GateOp.eval, fold_or_bit, List.map_map, Function.comp_def, getD_bits]
  · cases ei : g.inputs with
    | nil =>
      simp only [h,GateOp.eval,List.map_nil,List.headD_nil,Bool.not_false]
      rw [show (~~~(0 : W)) = BitVec.allOnes 64 from BitVec.not_zero,BitVec.getLsbD_allOnes]
      exact decide_eq_true r.isLt
    | cons a l => simp only [h,GateOp.eval,ei,List.map_cons,List.headD_cons,getD_bits,
        BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]

theorem run_bits (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (ws : List W) (r : Fin 64) :
    (gs.foldl stepWord ws).map (fun w => w.getLsbD r.val) =
      gs.foldl stepBool (ws.map fun w => w.getLsbD r.val) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons]
    rw [ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)), step_bits ws g (hgs g (by simp)) r]

def Tracks (s : Finset W) (z : W) : Prop := z = 0 ∨ z = -1 ∨ z ∈ s

abbrev Legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem from_word (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, Tracks s a) (j : ℕ) :
    Tracks s (ws.getD j 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => exact Or.inl rfl
  | some a => exact hw a (List.mem_of_getElem? h)

theorem const_ones : (-1 : W) = BitVec.allOnes 64 := by decide

theorem unary_move {s : Finset W} {a : W} (ha : Tracks s a) :
    Tracks s (~~~a) ∨ ∃ xs, Move true xs (~~~a) true ∧ xs.toFinset ⊆ s := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inr (Or.inl (by decide)))
  · exact Or.inl (Or.inl (by decide))
  by_cases h : Tracks s (~~~a)
  · exact Or.inl h
  · exact Or.inr ⟨[a],⟨fun hz => h (Or.inl hz),fun hz => h (Or.inr (Or.inl hz)),Or.inr ⟨a,rfl,rfl,rfl,rfl⟩⟩,by simpa using ha⟩


theorem binary_move {p : Bool} {s : Finset W} {a b z : W}
    (ha : Tracks s a) (hb : Tracks s b) (hz : z = a &&& b ∨ z = a ||| b) :
    Tracks s z ∨ ∃ xs, Move p xs z p ∧ xs.toFinset ⊆ s := by
  rcases ha with a0 | a1 | ha
  · rcases hz with hz | hz
    · rw [hz,a0]
      exact Or.inl (Or.inl (show (0 : W) &&& b = 0 from BitVec.zero_and))
    · rw [hz,a0,show (0 : W) ||| b = b from BitVec.zero_or]
      exact Or.inl hb
  · rcases hz with hz | hz
    · rw [hz,a1,const_ones,BitVec.allOnes_and]
      exact Or.inl hb
    · rw [hz,a1,const_ones,BitVec.allOnes_or]
      exact Or.inl (Or.inr (Or.inl const_ones.symm))
  · rcases hb with b0 | b1 | hb
    · rcases hz with hz | hz
      · rw [hz,b0]
        exact Or.inl (Or.inl (show a &&& (0 : W) = 0 from BitVec.and_zero))
      · rw [hz,b0,show a ||| (0 : W) = a from BitVec.or_zero]
        exact Or.inl (Or.inr (Or.inr ha))
    · rcases hz with hz | hz
      · rw [hz,b1,const_ones,BitVec.and_allOnes]
        exact Or.inl (Or.inr (Or.inr ha))
      · rw [hz,b1,const_ones,BitVec.or_allOnes]
        exact Or.inl (Or.inr (Or.inl const_ones.symm))
    · by_cases eq : a=b
      · subst b
        rcases hz with hz | hz
        · rw [hz,BitVec.and_self]; exact Or.inl (Or.inr (Or.inr ha))
        · rw [hz,BitVec.or_self]; exact Or.inl (Or.inr (Or.inr ha))
      · by_cases hc : Tracks s z
        · exact Or.inl hc
        · refine Or.inr ⟨[a,b],⟨fun hz => hc (Or.inl hz),fun hz => hc (Or.inr (Or.inl hz)),
            Or.inl ⟨a,b,rfl,eq,hz,rfl⟩⟩,?_⟩
          intro w hw
          simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hw
          rcases hw with rfl | rfl <;> assumption


theorem build_pad {k l} {p : Bool} {s : Finset W} (size : k ≤ l) (h : Build k p s) : Build l p s := by
  induction size with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_allow {k s} (h : Build k false s) : Build k true s := by
  induction k generalizing s with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | ⟨xs,z,q,mv,sub,more⟩
    · exact Or.inl (ih skip)
    rcases mv with ⟨n0,n1,⟨a,b,eq,ne,hz,rfl⟩ | ⟨a,_,_,bad,_⟩⟩
    · exact Or.inr ⟨xs,z,true,⟨n0,n1,Or.inl ⟨a,b,eq,ne,hz,rfl⟩⟩,sub,ih more⟩
    · contradiction

theorem gate_cases (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, Tracks s a)
    (g : Gate) (hg : Legal g) :
    Tracks s (gateWord ws g) ∨
      (g.op = GateOp.not ∧ ∃ xs, Move true xs (gateWord ws g) true ∧ xs.toFinset ⊆ s) ∨
      (g.op ≠ GateOp.not ∧ ∀ p, ∃ xs, Move p xs (gateWord ws g) p ∧ xs.toFinset ⊆ s) := by
  obtain ⟨op,xs⟩ := g
  rcases hg.1 with rfl | rfl | rfl
  · have max : xs.length ≤ 2 := hg.2
    rcases xs with _ | ⟨i,_ | ⟨j,_ | ⟨k,tail⟩⟩⟩
    · exact Or.inl (Or.inr (Or.inl (by simpa [gateWord] using const_ones.symm)))
    · exact Or.inl (by simpa only [gateWord,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
        BitVec.and_allOnes,show ∀ a : W, a ||| (0 : W) = a from fun _ => BitVec.or_zero] using from_word ws s hw i)
    · have reduce : gateWord ws ⟨GateOp.and,[i,j]⟩ = ws.getD i 0 &&& ws.getD j 0 := by
        simp only [gateWord,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,BitVec.and_allOnes]
      have hc (p) := binary_move (p := p) (from_word ws s hw i) (from_word ws s hw j) (Or.inl reduce)
      by_cases h : Tracks s (gateWord ws ⟨GateOp.and,[i,j]⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨by simp,fun p => (hc p).resolve_left h⟩)
    · simp at max
  · have max : xs.length ≤ 2 := hg.2
    rcases xs with _ | ⟨i,_ | ⟨j,_ | ⟨k,tail⟩⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (by simpa only [gateWord,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
        BitVec.and_allOnes,show ∀ a : W, a ||| (0 : W) = a from fun _ => BitVec.or_zero] using from_word ws s hw i)
    · have reduce : gateWord ws ⟨GateOp.or,[i,j]⟩ = ws.getD i 0 ||| ws.getD j 0 := by simp [gateWord]
      have hc (p) := binary_move (p := p) (from_word ws s hw i) (from_word ws s hw j) (Or.inr reduce)
      by_cases h : Tracks s (gateWord ws ⟨GateOp.or,[i,j]⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨by simp,fun p => (hc p).resolve_left h⟩)
    · simp at max
  · have get := unary_move (from_word ws s hw (xs.headD 0))
    have val : gateWord ws ⟨GateOp.not,xs⟩ = ~~~((xs.map (fun i => ws.getD i 0)).headD 0) := rfl
    cases xs with
    | nil => exact Or.inl (Or.inr (Or.inl (by change (~~~(0 : W)) = -1; decide)))
    | cons a tail => exact get.elim Or.inl (fun h => Or.inr (Or.inl ⟨rfl,h⟩))

theorem run_build (gs : List Gate) (hgs : ∀ g ∈ gs, Legal g) 
    (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, Tracks s a) (out : ℕ)
    (correct : (gs.foldl stepWord ws).getD out 0 = want) : Build gs.length true s := by
  induction gs generalizing ws s with
  | nil =>
    have got := from_word ws s hw out
    rw [List.foldl_nil] at correct
    rw [correct] at got
    exact got.resolve_left (by decide) |>.resolve_left (by decide)
  | cons g tail ih =>
    have tlegal : ∀ v ∈ tail, Legal v := fun v h => hgs v (List.mem_cons_of_mem _ h)
    have cases := gate_cases ws s hw g (hgs g List.mem_cons_self)
    rw [List.foldl_cons] at correct
    have progress (s' : Finset W) (sub : s ⊆ s') (added : Tracks s' (gateWord ws g)) :
        ∀ a ∈ stepWord ws g, Tracks s' a := by
      intro a ha
      simp only [stepWord,List.mem_append,List.mem_singleton] at ha
      rcases ha with ha | rfl
      · rcases hw a ha with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (sub h))
      · exact added
    rcases cases with ok | ⟨hop,xs,mv,hs⟩ | ⟨_,move⟩
    · exact Or.inl (ih tlegal _ s (progress s le_rfl ok) correct)
    · exact Or.inr ⟨xs,gateWord ws g,true,mv,hs,
        ih tlegal _ _ (progress _ (Finset.subset_insert _ _) (Or.inr (Or.inr (Finset.mem_insert_self _ _)))) correct⟩
    · obtain ⟨xs,mv,hs⟩ := move true
      exact Or.inr ⟨xs,gateWord ws g,true,mv,hs,
        ih tlegal _ _ (progress _ (Finset.subset_insert _ _) (Or.inr (Or.inr (Finset.mem_insert_self _ _)))) correct⟩

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))



theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨fun hm => (List.nodup_cons.mp habr).1 (List.mem_cons_of_mem _ hm),
        (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2⟩
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem finish_list {ws : List W} (nd : ws.Nodup) (h : ws.toFinset = {want}) : ws = [want] := by
  have hc := List.toFinset_card_of_nodup nd
  rw [h] at hc
  cases ws with
  | nil => simp at hc
  | cons a r =>
    cases r with
    | nil => simpa using h
    | cons b l => simp at hc

theorem singleton_kept {ws r : List W} {a : W} {t : Finset W}
    (perm : ws.Perm (a::r)) (nd : ws.Nodup)
    (set_eq : ws.toFinset = insert a t) :
    ∃ kept, (kept = r ∨ kept = a::r) ∧ kept.Nodup ∧ kept.toFinset=t := by
  have base : ws.toFinset = insert a r.toFinset := by ext w; simp [perm.mem_iff]
  have both := (perm.nodup_iff.mp nd)
  have without : ∀ w, w ∈ r ↔ w ∈ t ∧ w ≠ a := by
    intro w
    have he : (w ∈ insert a r.toFinset) ↔ (w ∈ insert a t) := by rw [← base,← set_eq]
    simp only [Finset.mem_insert,List.mem_toFinset] at he
    have notin := (List.nodup_cons.mp both).1
    grind
  by_cases ha : a ∈ t
  · refine ⟨a::r,Or.inr rfl,both,?_⟩
    ext w
    simp [without]
    grind
  · refine ⟨r,Or.inl rfl,(List.nodup_cons.mp both).2,?_⟩
    ext w
    simp [without]
    grind

theorem explored {k : ℕ} {p : Bool} {ws : List W} (hn : ws.Nodup)
    (h : Live k p ws.toFinset) : explore k p ws = true := by
  induction k generalizing p ws with
  | zero => simp [explore,finish_list hn h]
  | succ k ih =>
    rcases live_first h with done | ⟨xs,z,b,t,mv,hz,hws,tail⟩
    · simp [explore,finish_list hn done]
    have length : ws.length ≤ k+2 := by
      have hc := live_card h
      rwa [List.toFinset_card_of_nodup hn] at hc
    have zt : z ∉ t := fun hm => hz (hws ▸ Finset.mem_union_right _ hm)
    have tcard : t.card ≤ k := by
      have hc := live_card tail
      rw [Finset.card_insert_of_notMem zt] at hc
      omega
    have next {kept : List W} (hd : kept.Nodup) (ht : kept.toFinset=t) :
        explore k b (z :: kept) = true := by
      apply ih (List.nodup_cons.mpr ⟨fun m => zt (ht ▸ List.mem_toFinset.mpr m),hd⟩)
      simpa [ht] using tail
    have good {others : List W} (perm : ws.Perm others) : fresh z others = true := by
      have n0 : z ≠ 0 := mv.1
      have n1 : z ≠ -1 := mv.2.1
      have nh : z ∉ others := fun hm => hz (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
      simpa [fresh] using And.intro (And.intro n0 n1) nh
    rw [explore]
    rw [Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨⟨length,all_cuts h⟩,?_⟩
    rcases mv.2.2 with ⟨a,c,rfl,ne,form,rfl⟩ | ⟨a,rfl,rfl,rfl,rfl⟩
    · have sa : a ∈ ws := List.mem_toFinset.mp (by rw [hws]; simp)
      have sc : c ∈ ws := List.mem_toFinset.mp (by rw [hws]; simp)
      obtain ⟨r,hm,perm⟩ := pick_two sa sc ne
      have go {a c : W} (perm : ws.Perm (a::c::r))
          (set_eq : ws.toFinset = insert a (insert c t))
          (op : z ∈ [a &&& c, a ||| c]) : step2 k b (explore k) a c r = true := by
        obtain ⟨kept,hk,hnd,hfin⟩ := recover_kept perm hn set_eq
        have ht := next hnd hfin
        have le : kept.length ≤ k := by
          rw [← List.toFinset_card_of_nodup hnd,hfin]
          exact tcard
        have fr := good perm
        apply List.any_eq_true.mpr
        refine ⟨z,op,?_⟩
        rw [Bool.and_eq_true]
        refine ⟨fr,?_⟩
        simp only [keepChoices,List.mem_cons,List.not_mem_nil,or_false] at hk
        simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
        rcases hk with rfl | rfl | rfl | rfl <;> (try simp only [List.length_cons] at le)
        · exact Or.inl (Or.inl ht)
        · exact Or.inl (Or.inr ⟨by omega,Or.inl ht⟩)
        · exact Or.inl (Or.inr ⟨by omega,Or.inr ht⟩)
        · exact Or.inr ⟨by omega,ht⟩
      rw [Bool.or_eq_true]
      right
      apply List.any_eq_true.mpr
      have hset : ws.toFinset = insert a (insert c t) := by rw [hws]; simp
      rcases hm with hm | hm
      · exact ⟨(a,c,r),hm,go perm hset (by simpa using form)⟩
      · exact ⟨(c,a,r),hm,go (perm.trans (.swap _ _ _)) (by rw [hset,Finset.insert_comm])
          (by simpa [BitVec.and_comm c a,BitVec.or_comm c a] using form)⟩
    · have sz : ws.length ≤ k+1 := by
        have ub := Finset.card_insert_le a t
        rw [← List.toFinset_card_of_nodup hn,hws]
        simp at *
        omega
      have sa : a ∈ ws := List.mem_toFinset.mp (by rw [hws]; simp)
      obtain ⟨r,hm,perm⟩ := pick_one sa
      have set_eq : ws.toFinset = insert a t := by rw [hws]; simp
      obtain ⟨kept,hk,hnd,hfin⟩ := singleton_kept perm hn set_eq
      have hf := next hnd hfin
      have kl : kept.length ≤ k := by rw [← List.toFinset_card_of_nodup hnd,hfin]; exact tcard
      rw [Bool.or_eq_true]
      left
      simp only [Bool.and_eq_true,decide_eq_true_eq,true_and]
      refine ⟨sz,List.any_eq_true.mpr ⟨(a,r),hm,?_⟩⟩
      simp only [step1,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
      exact ⟨good perm,hk.elim (fun eq => Or.inl (eq ▸ hf)) (fun eq => Or.inr ⟨by rw [eq] at kl; simp at kl; omega,eq ▸ hf⟩)⟩

def adjacentSamples : List (ℕ × ℕ) := [(3,2),(3,1),(5,1),(9,1),(22,6)]

theorem required : ∀ a ∈ initial, ∃ rq ∈ adjacentSamples,
    want.getLsbD rq.1 = true ∧ want.getLsbD rq.2 = false ∧ rq.1 < 64 ∧ rq.2 < 64 ∧
      ∀ w ∈ initial, sep true rq.1 rq.2 w → w = a := by
  intro a ha
  simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · refine ⟨(3,2),by decide,by decide,by decide,by decide,by decide,?_⟩
    intro w hw
    simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold sep <;> decide +kernel
  · refine ⟨(3,1),by decide,by decide,by decide,by decide,by decide,?_⟩
    intro w hw
    simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold sep <;> decide +kernel
  · refine ⟨(5,1),by decide,by decide,by decide,by decide,by decide,?_⟩
    intro w hw
    simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold sep <;> decide +kernel
  · refine ⟨(9,1),by decide,by decide,by decide,by decide,by decide,?_⟩
    intro w hw
    simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold sep <;> decide +kernel
  · refine ⟨(22,6),by decide,by decide,by decide,by decide,by decide,?_⟩
    intro w hw
    simp only [initial,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> unfold sep <;> decide +kernel
theorem forcestart {t : Finset W} {k : ℕ} (sub : t ⊆ initial.toFinset)
    (hl : Live k true t) : t = initial.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  obtain ⟨⟨r,q⟩,_,pos,neg,hr,hq,unique⟩ := required a (List.mem_toFinset.mp ha)
  obtain ⟨w,hw,hsep⟩ := preserves_sep hl r q pos neg hr hq
  exact unique w (List.mem_toFinset.mp (sub hw)) hsep ▸ hw

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem neg0 : step1 6 (explore 6) 12297829382473034410 [14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem neg1 : step1 6 (explore 6) 14757395258967641292 [12297829382473034410,17361641481138401520,18374966859414961920,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem neg2 : step1 6 (explore 6) 17361641481138401520 [12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem neg3 : step1 6 (explore 6) 18374966859414961920 [12297829382473034410,14757395258967641292,17361641481138401520,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem neg4 : step1 6 (explore 6) 18446462603027742720 [12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op0_1 : step2 6 true (explore 6) 12297829382473034410 14757395258967641292 [17361641481138401520,18374966859414961920,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op0_2 : step2 6 true (explore 6) 12297829382473034410 17361641481138401520 [14757395258967641292,18374966859414961920,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op0_3 : step2 6 true (explore 6) 12297829382473034410 18374966859414961920 [14757395258967641292,17361641481138401520,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op0_4 : step2 6 true (explore 6) 12297829382473034410 18446462603027742720 [14757395258967641292,17361641481138401520,18374966859414961920] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op1_2 : step2 6 true (explore 6) 14757395258967641292 17361641481138401520 [12297829382473034410,18374966859414961920,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op1_3 : step2 6 true (explore 6) 14757395258967641292 18374966859414961920 [12297829382473034410,17361641481138401520,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op1_4 : step2 6 true (explore 6) 14757395258967641292 18446462603027742720 [12297829382473034410,17361641481138401520,18374966859414961920] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op2_3 : step2 6 true (explore 6) 17361641481138401520 18374966859414961920 [12297829382473034410,14757395258967641292,18446462603027742720] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op2_4 : step2 6 true (explore 6) 17361641481138401520 18446462603027742720 [12297829382473034410,14757395258967641292,18374966859414961920] = false := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem op3_4 : step2 6 true (explore 6) 18374966859414961920 18446462603027742720 [12297829382473034410,14757395258967641292,17361641481138401520] = false := by decide +kernel

theorem list_singles : singles initial = [(12297829382473034410,[14757395258967641292,17361641481138401520,18374966859414961920,18446462603027742720]),(14757395258967641292,[12297829382473034410,17361641481138401520,18374966859414961920,18446462603027742720]),(17361641481138401520,[12297829382473034410,14757395258967641292,18374966859414961920,18446462603027742720]),(18374966859414961920,[12297829382473034410,14757395258967641292,17361641481138401520,18446462603027742720]),(18446462603027742720,[12297829382473034410,14757395258967641292,17361641481138401520,18374966859414961920])] := rfl

theorem unary_zero : (singles initial).any (fun (a,r) => step1 6 (explore 6) a r) = false := by
  rw [list_singles]
  simp only [List.any_cons,List.any_nil]
  rw [neg0,neg1,neg2,neg3,neg4]
  rfl

theorem list_pairs : pairs initial = [(12297829382473034410,14757395258967641292,[17361641481138401520,18374966859414961920,18446462603027742720]),(12297829382473034410,17361641481138401520,[14757395258967641292,18374966859414961920,18446462603027742720]),(12297829382473034410,18374966859414961920,[14757395258967641292,17361641481138401520,18446462603027742720]),(12297829382473034410,18446462603027742720,[14757395258967641292,17361641481138401520,18374966859414961920]),(14757395258967641292,17361641481138401520,[12297829382473034410,18374966859414961920,18446462603027742720]),(14757395258967641292,18374966859414961920,[12297829382473034410,17361641481138401520,18446462603027742720]),(14757395258967641292,18446462603027742720,[12297829382473034410,17361641481138401520,18374966859414961920]),(17361641481138401520,18374966859414961920,[12297829382473034410,14757395258967641292,18446462603027742720]),(17361641481138401520,18446462603027742720,[12297829382473034410,14757395258967641292,18374966859414961920]),(18374966859414961920,18446462603027742720,[12297829382473034410,14757395258967641292,17361641481138401520])] := rfl

theorem binary_zero : (pairs initial).any (fun (a,b,r) => step2 6 true (explore 6) a b r) = false := by
  rw [list_pairs]
  simp only [List.any_cons,List.any_nil]
  rw [op0_1,op0_2,op0_3,op0_4,op1_2,op1_3,op1_4,op2_3,op2_4,op3_4]
  rfl

theorem exhausted : explore 7 true initial = false := by
  rw [explore,unary_zero,binary_zero]
  simp [initial]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4278124266 * 2 ^ 32 + 4277071594)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.and,[1,2]⟩,⟨.or,[0,6]⟩,⟨.and,[3,4]⟩,⟨.or,[8,5]⟩,⟨.and,[2,9]⟩,
    ⟨.or,[1,10]⟩,⟨.or,[3,4]⟩,⟨.and,[11,12]⟩,⟨.or,[7,13]⟩],14⟩

theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxHeartbeats 2000000 in
theorem witness_ok : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

def fixedFn (x : Fin 5 → Bool) : Bool :=
  Nat.testBit 4008241832 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

theorem inputs_eval : ∀ r : Fin 64, initial.map (fun w => w.getLsbD r.val) =
    List.ofFn (fun i : Fin 5 => r.val.testBit i.val) := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem want_eval : ∀ r : Fin 64, want.getLsbD r.val =
    fixedFn (fun i : Fin 5 => r.val.testBit i.val) := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem minimum (excluded : explore 7 true initial = false) (s : ℕ)
    (h : HasCircuitSize 5 fixedFn s) : 8 ≤ s := by
  obtain ⟨C,ok,budget,correct⟩ := h
  by_contra! small
  let out := (C.gates.foldl stepWord initial).getD C.output 0
  have eq : out = want := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change ((C.gates.foldl stepWord initial).getD C.output 0).getLsbD i = want.getLsbD i
    rw [← getD_bits,run_bits C.gates ok initial ⟨i,hi⟩,inputs_eval ⟨i,hi⟩]
    change C.eval (List.ofFn (fun j : Fin 5 => i.testBit j.val)) = _
    exact (correct _).trans (want_eval ⟨i,hi⟩).symm
  have build := run_build C.gates ok initial initial.toFinset
    (fun w hm => Or.inr (Or.inr (List.mem_toFinset.mpr hm))) C.output eq
  have sz : C.gates.length ≤ 7 := by
    change C.gates.length ≤ s at budget
    omega
  obtain ⟨t,ht,live⟩ := build_live (build_pad sz build)
  have live_init : Live 7 true initial.toFinset := forcestart ht live ▸ live
  have hit : explore 7 true initial = true := explored (by decide) live_init
  exact Bool.false_ne_true (excluded.symm.trans hit)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this



def rotation (i : Fin 6) : Fin 6 := ![5,0,1,2,3,4] i
def moved (x : Fin 6 → Bool) : Bool := target (x ∘ rotation)

set_option maxHeartbeats 2000000 in
theorem pin_eval : ∀ x : Fin 5 → Bool, moved (Fin.snoc x false) = fixedFn x := by decide +kernel

theorem original_minimum (s : ℕ) (h : HasCircuitSize 6 target s) : 9 ≤ s := by
  have permuted : HasCircuitSize 6 moved s := relabel_size rotation target s h
  have dep : ∃ x : Fin 6 → Bool, moved (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ moved x :=
    ⟨fun _ => false, by decide⟩
  have nc : ∃ y y' : Fin 5 → Bool, moved (Fin.snoc y false) ≠ moved (Fin.snoc y' false) :=
    ⟨fun _ => false, fun j => (3 : ℕ).testBit j.val, by decide⟩
  obtain ⟨t,ht,hT⟩ := gate_elim_one 5 moved false s dep nc permuted
  rw [show (fun x : Fin 5 → Bool => moved (Fin.snoc x false)) = fixedFn from funext pin_eval] at hT
  have hmin := minimum exhausted t hT
  omega

end PEqualNP.Outside.L_meta_13185_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_13185_aux

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_13185 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277071594) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277071594) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  exact ⟨witness,witness_mono,original_minimum s h,witness_ok⟩
