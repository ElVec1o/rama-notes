#!/bin/bash
# Run the adversarial search single-threaded and at low priority.
# numpy on macOS uses Accelerate, which otherwise spawns a thread per core; pinning
# to one keeps this from saturating the machine during a long search.
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
       VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1
exec nice -n 15 python3 -u "$(dirname "$0")/hl_Xsign.py"
