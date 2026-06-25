#!/usr/bin/env python3
"""Decoupe la sortie du workflow audit-couverture-ch1-ch4 en deux JSON {sections:[...]}
pour gen_couverture.py (CHAP_I et CHAP_IV)."""
import sys
import json


def find_key(o, key):
    if isinstance(o, dict):
        if key in o and isinstance(o[key], list):
            return o[key]
        for v in o.values():
            r = find_key(v, key)
            if r is not None:
                return r
    elif isinstance(o, list):
        for v in o:
            r = find_key(v, key)
            if r is not None:
                return r
    return None


src = sys.argv[1]
outdir = sys.argv[2]
data = json.load(open(src, encoding="utf-8", errors="replace"))
ch1 = find_key(data, "ch1")
ch4 = find_key(data, "ch4")
if ch1 is None or ch4 is None:
    print("ECHEC: ch1/ch4 introuvables")
    sys.exit(2)
json.dump({"sections": ch1}, open(outdir + "/_audit_ch1.json", "w", encoding="utf-8"), ensure_ascii=False)
json.dump({"sections": ch4}, open(outdir + "/_audit_ch4.json", "w", encoding="utf-8"), ensure_ascii=False)
n1 = sum(len(s.get("notions", [])) for s in ch1)
n4 = sum(len(s.get("notions", [])) for s in ch4)
print("ch1: %d sections, %d notions" % (len(ch1), n1))
print("ch4: %d sections, %d notions" % (len(ch4), n4))
