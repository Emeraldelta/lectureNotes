// #Sireum #Logika

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._



@pure def orComm(p: B, q: B): Unit = {
    Deduce(
        (p | q) |- (q | p)
        Proof(
            //PROOF GOES HERE
            1 ( p | q ) by Premise,
            
            //use orE subproofs
            2 SubProof(
                //case where p is true
                3 Assume( p ),
                4 ( q | p ) by OrI2(3)
            ),
            5 SubProof(
                //case where q is true
                6 Assume( q ),
                7 ( q | p ) by OrI1(6)
            ),
            8 ( q | p ) by OrE(1, 2, 5)

        )
    )
}