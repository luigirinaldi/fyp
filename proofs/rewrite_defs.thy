theory rewrite_defs
    imports Main 
begin

definition "bw (p::nat) (a::int) = a mod 2^p"
(* assuming b can always be cast to a nat *)
definition "shl (a::int) (b::int) = a * 2^(nat(b))"
definition "shr (a::int) (b::int) = a div 2^(nat(b))"
definition "sel (c::int) (a::int) (b::int) = (a * (bw 1 c)) + (b * (bw 1 (not (bw 1 c))))"
definition "signed (p::nat) (a::int) = (bw p (2 * (bw (p - 1) a))) - (bw p a)"

syntax
    "shl" :: "int => int => int" ("_ << _")
    "shr" :: "int => int => int" ("_ >> _")
end