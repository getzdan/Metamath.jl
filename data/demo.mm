$c  wff  $.        $( we use this constant as a type of formula (well formed formula) $)
$c  ( ) ! ->  $.   $( brackets, negation, implication $)

$v  A B C  $.      $( variables to be used in formulas $)

wa  $f  wff A  $.  $( hypothesis "wa" which says, that A is a well-formed formula $)
wb  $f  wff B  $.
wc  $f  wff C  $.

$( Following assertions define the rules to create formulas $)
wng  $a wff ! A $.           $( mandatory hypotheses are (wa) $)
wim  $a wff ( A -> B ) $.    $( mandatory hypotheses are (wa, wb) $)

$c  |-  $.         $( this constant will be used as a type of provable formula  $)

$( Schemes of axioms of propositional logic $)
a1  $a |- ( A -> ( B -> A ) ) $.
a2  $a |- (    ( A -> ( B -> C ) )   ->    ( ( A -> B ) -> ( A -> C ) )    ) $.
a3  $a |- ( ( ! A -> ! B )  ->  ( B -> A ) ) $.  

$( new scope; otherwise mp1, mp2 will become mandatory for all upcoming assertions $)
${                               $( Modus Ponens rule of inference $)
    mp1 $e |- A $.                
    mp2 $e |- ( A -> B ) $.
    mp  $a |- B $.               $( mandatory hypotheses of "mp" are (wa, wb, mp1, mp2) $)
$}


formula1 $p  wff ( A -> ( B -> C ) )  $= wa wb wc wim wim $.

formula2 $p  |- ( ( A -> A ) -> ( A -> A ) )  $= wa wa wa wim wim    
                                                 wa wa wim wa wa wim  wim  
                                                 wa wa a1    
                                                 wa wa wa a2    
                                                 mp  $.
												 
												 
th1  $p  wff ( A -> ( A -> A ) )  $=  wa wa wa wim wim  $.
th2  $p  wff ( ( A -> A ) -> ( A -> A ) )  $=  wa wa wim wa wa wim  wim  $.
th3  $p  |-  ( A -> ( A -> A ) )  $=  wa wa a1  $.
th4  $p  |-  (  ( A -> ( A -> A ) )  ->  ( ( A -> A ) -> ( A -> A ) ) )  $=  wa wa wa a2  $.
