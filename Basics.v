(** **** Exercise: 1 star, standard (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match (andb b1 b2) with
  | true => false
  | false => true
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. unfold nandb. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. unfold nandb. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. unfold nandb. simpl. reflexivity. Qed.

(** **** Exercise: 1 star, standard (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 && b2 && b3 with
  | true => true
  | false => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. unfold andb3. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. unfold andb3. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. unfold andb3. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. unfold andb3. simpl. reflexivity. Qed.
