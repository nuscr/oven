%{

open Syntax

let block_to_global = function
  | [g] -> g (* if it is one then no sequence *)
  | gs -> Seq gs (* if it is zero or more than one then it is a sequence *)

let rec build f = function
  | [] -> Seq []
  | [g] -> g
  | g::gs -> f g @@ build f gs

let unpack_message_transfer = function
  | MessageTransfer lbl -> lbl
  | _ -> Error.Violation "Expected a MessageTransfer." |> raise

%}

(* ---------------------------------------- *)

%token <string>IDENT
%token <int>INT

%token EOI

%token COMMA
%token SEMICOLON
%token LPAR
%token RPAR
%token LCURLY
%token RCURLY

(* keywords from Scribble.g with original comments *)
%token PROTOCOL_KW
%token GLOBAL_KW
%token ROLE_KW

%token FROM_KW
%token TO_KW
%token OR_KW
%token AND_KW
%token CHOICE_KW

%token REC_KW
%token CONTINUE_KW

%token FIN_KW
%token INF_KW
%token PAR_KW
%token WEAK_KW

%token INTERSECTION_KW
%token JOIN_KW

%token PRIORITISE_KW
%token WITH_KW
%token HIGH_KW
%token LOW_KW


(* pragmas *)
/* %token PRAGMA_START */
/* %token PRAGMA_END */

(* ---------------------------------------- *)
%start < compilation_unit > cu

%%

/* let pragma_value := */
/*   | COLON ; v = IDENT ; { v } */

/* let pragma_decl := */
/*   | k = IDENT ; v = pragma_value? ; { Pragma.pragma_of_string k , v } */

/* (* pragmas *) */
/* let pragmas := */
/*   | PRAGMA_START; ps = separated_list(COMMA, pragma_decl) ; PRAGMA_END ; { ps } */

(* A file is parsed into a compilation unit *)
let cu :=
  /* pgs = pragmas? ; (* Pragma must be at the beginning of a file *) */
  ps = global_protocol_decl* ;
  EOI ;
    {
      ps
    }


(* protocols *)

let global_protocol_decl ==
  protocol_hdr ; nm = name ;
  rs = role_decls ;
  body = global_protocol_body ;
  {
    { protocol_name = nm
    ; roles = rs
    ; interactions = body
    }
  }

let protocol_hdr ==
  GLOBAL_KW ; PROTOCOL_KW? ; { () }
  | PROTOCOL_KW ; { () }

let role_decls == LPAR ; nms = separated_nonempty_list(COMMA, role_decl) ;
                  RPAR ; { nms }

let role_decl == ROLE_KW? ; nm = name ; { nm }

let global_protocol_body ==
  LCURLY ; ints = global_interaction* ;
  RCURLY ; { block_to_global ints }

let global_interaction ==
  global_message_transfer
  | global_choice
  | inf_composition
  | fin_composition
  | rec_composition
  | var_composition
  | parallel_composition
  | weak_composition
  | join_composition
  | intersection
  | priority
  | global_protocol_block


let global_protocol_block ==
  LCURLY ; ints = global_interaction* ; RCURLY ; { block_to_global ints }

let inf_composition ==
  INF_KW ; ~ = global_protocol_block ; < Inf >

let fin_composition ==
  FIN_KW ; ~ = global_protocol_block ; < Fin >

let rec_composition ==
  REC_KW ; ~ = name ;  ~ = global_protocol_block ; < Rec >

let var_composition ==
  CONTINUE_KW ; ~ = name ; SEMICOLON? ; < Var >

let parallel_composition ==
  PAR_KW ;
  ~ = separated_nonempty_list(AND_KW, global_protocol_block) ;
  < Par >

let weak_composition ==
  WEAK_KW ;
  gs = separated_nonempty_list(AND_KW, global_protocol_block) ;
  { build (fun g1 g2 -> OutOfOrder (g1, g2)) gs }

let join_composition ==
  JOIN_KW ;
  gs = separated_nonempty_list(AND_KW, global_protocol_block) ;
  { build (fun g1 g2 -> Join (g1, g2)) gs }

let intersection ==
  INTERSECTION_KW ;
  gs = separated_nonempty_list(AND_KW, global_protocol_block) ;
  { build (fun g1 g2 -> Intersection (g1, g2)) gs }

let priority ==
  PRIORITISE_KW ; p1 = global_protocol_block ;
  WITH_KW ; HIGH_KW ; p2 = global_message_transfer ;
  WITH_KW ; LOW_KW ; p3 = global_message_transfer ;
  { Prioritise (p1, unpack_message_transfer p2, unpack_message_transfer p3) }

let global_choice ==
  CHOICE_KW ;
  ~ = separated_nonempty_list(OR_KW, global_protocol_block) ;
  < Choice >

let global_message_transfer ==
  msg = message ; FROM_KW ; frn = name ;
  TO_KW ; ton = name ;
  SEMICOLON ;
  { MessageTransfer {label = msg ; sender = frn ; receiver  = ton } }

let message ==
  msg = message_signature ; { msg }
  | nm = name ; { { name = nm ; payloads = [] } }

let message_signature ==
  | nm = name ; LPAR ; pars=separated_list(COMMA, name) ; RPAR ;
      { { Syntax.name = nm
        ; Syntax.payloads = pars
        }
      }

let name ==
  | i = IDENT ; { i }
  | i = INT ; { string_of_int i }
