#!/usr/bin/env python3
"""mcscore — print the calibrated machine-cost verdict for one SLP
triple: '<delayed> <eligible>/16 <boundary>' (or REJECT on parse/dims
failure). Used by ourslane.sh to gate and rank optimizer outputs."""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import machinecost as mc


def main():
    lp, rp, pp = sys.argv[1:4]
    try:
        L, R, P = mc.parse(lp), mc.parse(rp), mc.parse(pp)
        (lin, lout), (rin, rout), (pin, pout) = (
            mc.dims(L), mc.dims(R), mc.dims(P))
        if not (lin == rin == 16 and lout == rout == 48 and pout == 16):
            print("REJECT dims")
            return
        nprod = lout
        sc = (mc.scalar_cost(L) + mc.scalar_cost(R)
              + nprod * mc.C_MUL + mc.scalar_cost(P))
        pdc, ne, no, nb, npe = mc.p_delayed(P)
        dl = min(mc.scalar_cost(L) + mc.scalar_cost(R) + npe * mc.D_MUL
                 + (nprod - npe) * mc.C_MUL + pdc, sc)
        print(f"{dl:.1f} {ne}/16 {nb}")
    except Exception as e:
        print(f"REJECT {e}")


if __name__ == "__main__":
    main()
