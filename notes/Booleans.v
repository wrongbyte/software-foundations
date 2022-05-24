(** Boolean stuff**)
Inductive bool : Type :=
  | true
  | false.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool): bool :=
  match b1 with
  | false => false
  | true => b2
  end.

Definition orb (b1: bool) (b2: bool): bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition xorb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => negb(b2)
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example xor_1: (xorb true false) = true.
Proof. simpl. reflexivity. Qed.

Example xor_2: (xorb true true) = false.
Proof. simpl. reflexivity. Qed.

Example xor_3: (xorb false true) = true.
Proof. simpl. reflexivity. Qed.

Example xor_4: (xorb false false)   = false.
Proof. simpl. reflexivity. Qed.