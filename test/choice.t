run choice.oven
  $ oven ./choice.oven
  // ovenMPST - Local state machines for: ./choice.oven
  // Protocol: Borked
  // Role: C
  digraph G {
    rankdir=LR;
    0 [label="0", shape=circle, ];
    1 [label="E-1", fillcolor="#FF7777", shape=doublecircle, style="filled", ];
    2 [label="S-2", fillcolor="#77FF77", shape=circle, style="filled", ];
    3 [label="3", shape=circle, ];
    
    
    0 -> 1 [label="C!S<DONE>", ];
    2 -> 0 [label="C!S<B>", ];
    2 -> 1 [label="C!S<DONE>", ];
    2 -> 3 [label="C!S<A>", ];
    3 -> 1 [label="C!S<DONE>", ];
    3 -> 3 [label="C!S<A>", ];
    
    }
  // Role: S
  digraph G {
    rankdir=LR;
    0 [label="0", shape=circle, ];
    1 [label="E-1", fillcolor="#FF7777", shape=doublecircle, style="filled", ];
    2 [label="S-2", fillcolor="#77FF77", shape=circle, style="filled", ];
    3 [label="3", shape=circle, ];
    
    
    0 -> 1 [label="C?S<DONE>", ];
    2 -> 0 [label="C?S<B>", ];
    2 -> 1 [label="C?S<DONE>", ];
    2 -> 3 [label="C?S<A>", ];
    3 -> 1 [label="C?S<DONE>", ];
    3 -> 3 [label="C?S<A>", ];
    
    }
