(*TIME
Require Import Timing.
*)

Ltac time_abstract t := 
  (*TIME time "all:outside" ( *)
  abstract 
  (*TIME (time "all:inside" *) t (*TIME )) *).
 