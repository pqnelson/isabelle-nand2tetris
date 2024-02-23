This is [Nand2Tetris](https://www.nand2tetris.org/) formalized in
Isabelle/HOL, specifically the hardware-level abstractions. The only
"primitive" is the NAND logic gate for combinational circuitry.

The natural way to model circuitry in HOL is Anthony Fox's trick to use
the "Devices as Logical Relations" idiom, `Gate[in, out]`. 

We use the "intuitive" alternative using functions as relations. NAND is
a function, `NAND`. But then how do we deal with sequential logic
like latches, registers, and RAM?

One possibility is to use monads, but if we use monads for a 1-bit cell,
forming a 16-bit register becomes...tedious. Furthermore, this abstracts
away time: every change occurs instantaneously, and resolves without a
problem. 

The second possibility is to use codatatypes for signals as repeating
bits, as measured according to a global clock. The disadvantage with
this approach is that it will not model issues where combinational gates
have different clock frequencies (which could result in instability
issues, metastability, etc.). But we are not terribly interested in
these situations, so we just assume the hardware is synchronized
adequately. 


> What is a scientist after all? It is a curious man looking through a
> keyhole, the keyhole of nature, trying to know what's going on. 
>
> --- Jacques-Yves Cousteau, Christian Science Monitor (21 July 1971)

> All explorers are seeking something they have lost. It is seldom that
> they find it, and more seldom still that the attainment brings them
> greater happiness than the quest. 
> 
> --- Arthur C. Clarke, _The City and the Stars_ (1956)