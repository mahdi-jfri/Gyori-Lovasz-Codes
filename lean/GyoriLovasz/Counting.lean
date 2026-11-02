import GyoriLovasz.Potential

namespace GyoriLovasz

theorem nodup_length_le_of_subset {xs ys : List α} (hx : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) : xs.length ≤ ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hx
    have hm := hsub x (by simp)
    have ht : ∀ y, y ∈ xs → y ∈ ys.erase x := by
      intro y hy
      have hne : y ≠ x := by intro he; subst y; exact hnot hy
      exact (List.mem_erase_of_ne hne).mpr (hsub y (by simp [hy]))
    have hl := ih hnd ht
    have he := List.length_erase_of_mem hm
    simp only [List.length_cons]
    have hpos : 0 < ys.length := List.length_pos_iff.mpr (by
      intro he; subst ys; simp at hm)
    omega

theorem countTrue_filter_length (xs : List α) (P : α → Prop) [DecidablePred P] :
    countTrue xs P = (xs.filter (fun x => decide (P x))).length := by
  classical
  induction xs with
  | nil => simp [countTrue]
  | cons x xs ih =>
    by_cases h : P x <;> simp [countTrue, h, ih, Nat.add_comm]

theorem size_eq_countTrue (xs : List α) (C : Cut α) :
    size xs C = countTrue xs (fun x => C x = Side.sep) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : C x <;> simp [size, countTrue, h, Side.weight, ih]

theorem countTrue_congr (xs : List α) {P Q : α → Prop}
    (h : ∀ x, x ∈ xs → (P x ↔ Q x)) : countTrue xs P = countTrue xs Q := by
  have h1 := countTrue_mono xs (fun x hx => (h x hx).mp)
  have h2 := countTrue_mono xs (fun x hx => (h x hx).mpr)
  omega

theorem countTrue_eq_length (xs : List α) (P : α → Prop)
    (h : ∀ x, x ∈ xs → P x) : countTrue xs P = xs.length := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp [countTrue, hx, ht, Nat.add_comm]

theorem countTrue_append (xs ys : List α) (P : α → Prop) :
    countTrue (xs ++ ys) P = countTrue xs P + countTrue ys P := by
  induction xs with
  | nil => simp [countTrue]
  | cons x xs ih => simp [countTrue, ih, Nat.add_assoc]

theorem countTrue_map (xs : List α) (f : α → β) (P : β → Prop) :
    countTrue (xs.map f) P = countTrue xs (fun x => P (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [countTrue, ih]

theorem countTrue_perm {xs ys : List α} (h : xs.Perm ys) (P : α → Prop) :
    countTrue xs P = countTrue ys P := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [countTrue, ih]
  | swap x y xs => simp [countTrue]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem nodup_map_of_injective {xs : List α} (h : xs.Nodup) (f : α → β)
    (hf : ∀ x y, f x = f y → x = y) : (xs.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (fun hne he => hne (hf _ _ he)) h

theorem nodup_subset_perm_of_length {xs ys : List α} (hx : xs.Nodup)
    (hsub : ∀ x, x ∈ xs → x ∈ ys) (hlen : xs.length = ys.length) : xs.Perm ys := by
  classical
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys; exact .nil
  | cons x xs ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hx
    have hm := hsub x (by simp)
    have ht : ∀ y, y ∈ xs → y ∈ ys.erase x := by
      intro y hy
      have hne : y ≠ x := by intro he; subst y; exact hnot hy
      exact (List.mem_erase_of_ne hne).mpr (hsub y (by simp [hy]))
    have he := List.length_erase_of_mem hm
    have hl : xs.length = (ys.erase x).length := by simp only [List.length_cons] at hlen; omega
    exact ((ih hnd ht hl).cons x).trans (List.perm_cons_erase hm).symm

theorem nodup_perm_of_same_mem {xs ys : List α} (hx : xs.Nodup) (hy : ys.Nodup)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.Perm ys := by
  have hle := nodup_length_le_of_subset hx (fun x => (hm x).mp)
  have hge := nodup_length_le_of_subset hy (fun x => (hm x).mpr)
  exact nodup_subset_perm_of_length hx (fun x => (hm x).mp) (by omega)

theorem map_nodup_injOn {xs : List α} {f : α → β} (hn : (xs.map f).Nodup)
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (he : f a = f b) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      rcases List.mem_cons.mp hb with hb | hb
      · exact hb.symm
      · exact False.elim (hnot (List.mem_map.mpr ⟨b, hb, he.symm⟩))
    · rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact False.elim (hnot (List.mem_map.mpr ⟨a, ha, he⟩))
      · exact ih htail ha hb

theorem exists_minimal_nat (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  have aux : ∀ n, P n → ∃ m, P m ∧ ∀ j, P j → m ≤ j := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hp
      by_cases hmin : ∀ j, P j → n ≤ j
      · exact ⟨n, hp, hmin⟩
      · obtain ⟨j, hj⟩ := Classical.not_forall.mp hmin
        have hpj : P j := by
          by_cases h : P j
          · exact h
          · exact False.elim (hj (fun h' => False.elim (h h')))
        have hlt : j < n := by
          have hnot : ¬n ≤ j := fun h => hj (fun _ => h)
          omega
        exact ih j hlt hpj
  obtain ⟨n, hn⟩ := h
  exact aux n hn

def sumValues (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumValues rest f

theorem sumValues_mono (xs : List α) {f g : α → Nat}
    (h : ∀ x, x ∈ xs → f x ≤ g x) : sumValues xs f ≤ sumValues xs g := by
  induction xs with
  | nil => simp [sumValues]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [sumValues]
    omega

theorem sumValues_strict (xs : List α) {f g : α → Nat}
    (h : ∀ x, x ∈ xs → f x ≤ g x)
    (strict : ∃ x, x ∈ xs ∧ f x < g x) : sumValues xs f < sumValues xs g := by
  induction xs with
  | nil => simp at strict
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ y, y ∈ xs → f y ≤ g y := fun y hy => h y (by simp [hy])
    obtain ⟨y, hy, hylt⟩ := strict
    rcases List.mem_cons.mp hy with he | he
    · subst y
      have hl := sumValues_mono xs ht
      simp only [sumValues]
      omega
    · have hl := ih ht ⟨y, he, hylt⟩
      simp only [sumValues]
      omega

theorem sumValues_const (xs : List α) (c : Nat) :
    sumValues xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => simp [sumValues]
  | cons x xs ih => simp [sumValues, ih, Nat.add_mul, Nat.add_comm]

end GyoriLovasz
