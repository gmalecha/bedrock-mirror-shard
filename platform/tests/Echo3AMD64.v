Require Import Bedrock Echo3Driver AMD64_gas.

Module M.
  Definition heapSize := 1024.
End M.

Module E := Make(M).

Set Printing Depth 999999.
Eval compute in moduleS E.m.