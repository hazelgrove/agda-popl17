Agda Mode Entry Cheatsheet
==========================

We have tried to stay as close to the on-paper notation as possible In
formalizing the metatheory of Hazelnut. This means using some special
characters in the souce code here to match the mathematical description in
the write up of the paper.

This file describes how to use the emacs agda input mode to enter each of
those special characters, in roughly the order that they appear in
`core.agda` broken into categories that aren't quite disjoint.

http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.UnicodeInput is a
good resource for wrangling this sort of thing.


Agda built-ins or prelude-defined types
------------------------------
 - "→" is `\to`

 - "⊤" is `\top`

 - "⊥" is `\bot`

 - "∀" is `\forall`

 - "∈" is `\in`

 - "×" is `\times` or `\x`, and not to be confused with "x"

 - subscripted numbers like "₂" are `\_2` after the main glyph is entered


judgemental and expression forms
--------------------------------
 - "⊢" is `\vdash`

 - "·" is `\cdot`

 - greek letters like "Γ", "Σ", "λ", "α", and "δ" are their names with
   relevant capitalization, so `\Gamma`, `\Sigma`, `\lambda`, `\alpha`,
   and `\delta`

 - "∘" is `\circ` or `\o`

 - "~̸" is `~\not`


super-scripted letters
----------------------

 - "τ̇" is `\tau \^.`

 - "ė" is `e \^.`

 - "τ̂" is `\tau \^`

 - "ê" is `e \^`


arrows
------

 - "▹" is `\t 2`

 - "◃" is `\t 6`

 - "▸" is `\t 5`

 - "◆" is `\di`

holes
-----
 - "⦇" "⦈" are `C-x 8 Z NOTATION LEFT IMAGE BRACKET` and `Z NOTATION RIGHT IMAGE BRACKET` respectively, per http://www.fileformat.info/info/unicode/char/2988/index.htm
