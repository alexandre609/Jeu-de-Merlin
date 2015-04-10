Require Import Bool.
Require Import List.
Require Import NArith.
Require Import Omega.

Definition plateau := (bool*bool*bool*bool*bool*bool*bool*bool*bool)%type.

Inductive coord_aux : Type :=
| a : coord_aux
| b : coord_aux
| c : coord_aux.

Definition coord := (coord_aux * coord_aux)%type.

Definition partie := (list coord)%type.

Function applique_clic (Plat : plateau) (Coord : coord) : plateau :=
match Coord with
|(a,a)=> match Plat with (A,B,C,D,E,F,G,H,J) => (negb(A),negb(B),C,negb(D), negb(E),F,G,H,J) end
|(a,b)=> match Plat with (A,B,C,D,E,F,G,H,J) => (negb(A),negb(B),negb(C),D, E,F,G,H,J) end
|(a,c)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,negb(B),negb(C),D, negb(E),negb(F),G,H,J) end
|(b,a)=> match Plat with (A,B,C,D,E,F,G,H,J) => (negb(A),B,C,negb(D), E,F,negb(G),H,J) end
|(b,b)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,negb(B),C,negb(D), negb(E),negb(F),G,negb(H),J) end
|(b,c)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,negb(C),D, E,negb(F),G,H,negb(J)) end
|(c,a)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,C,negb(D), negb(E),F,negb(G),negb(H),J) end
|(c,b)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,C,D, E,F,negb(G),negb(H),negb(J)) end
|(c,c)=> match Plat with (A,B,C,D,E,F,G,H,J) => (A,B,C,D, negb(E),negb(F),G,negb(H),negb(J)) end
end.

Fixpoint applique_partie
(Plat : plateau) (Part : partie) : plateau :=
match Part with
| Coord :: l => applique_partie (applique_clic Plat Coord) l
| nil => Plat
end.

Definition plateau_init_test : plateau := (false,false,false,false,false,false,false,false,false).

Definition plateau_gagnant (Plat : plateau) : Prop :=
Plat = (true,true,true,true,true,true,true,true,true).

Definition partie_gagnante (Plat : plateau) (Part : partie) : Prop :=
plateau_gagnant(applique_partie Plat Part).

Theorem exists_partie_gagnante_pour_init_test :
    exists p, partie_gagnante plateau_init_test p.
Proof.
exists ((a,a)::(a,c)::(c,c)::(c,a)::(b,b)::nil).
unfold partie_gagnante.
simpl.
unfold plateau_gagnant.
reflexivity.
Qed.

(*Lemma double_clic : forall (Plat:plateau), forall (Coord : coord),
applique_clic(applique_clic Plat Coord) Coord = Plat.
intros.*)
