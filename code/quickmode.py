"""Shared --quick handling, so a long search can be baselined without being rewritten.

Half the scripts the two papers cite had no recorded baseline, because they exceed the citation
check's per-script budget; drift in them was therefore invisible while the tool reported that
every cited script runs. `--quick` is the fix: it shrinks the wall-clock budget so a deterministic
baseline can be taken in seconds.

Two things have to be true for such a baseline to mean anything.

  IT MUST BE FRESH. Many of these scripts checkpoint into private/, and a checkpointed run
  resumes, so its output depends on however much compute has accumulated. That is exactly the
  defect found in jensen_sweep's snapshot. Under --quick the checkpoint is redirected to a
  scratch file, so the run starts empty and its output is a function of the code alone.

  IT MUST NOT DESTROY ANYTHING. The real checkpoints hold finished compute, in one case 1425
  items. `ckpt` never returns the real path under --quick and never writes to it, so a quick run
  cannot touch them.
"""

import os
import sys
import tempfile

QUICK = '--quick' in sys.argv
if QUICK:
    # Removed once recorded, because several of these scripts read their parameters positionally
    # out of sys.argv and would otherwise try to parse the flag as a number.
    sys.argv = [a for a in sys.argv if a != '--quick']


def budget(full, quick=25.0):
    """Wall-clock budget in seconds: the script's own value, or a small one under --quick."""
    return quick if QUICK else full


def scale(full, quick):
    """Any other size knob -- iteration caps, sample counts, vertex caps."""
    return quick if QUICK else full


def ckpt(path):
    """Checkpoint path, redirected to a scratch file under --quick so the run starts fresh.

    The scratch file is deleted first, so repeated quick runs are identical rather than
    accumulating, and the real path is never opened.
    """
    if not QUICK:
        return path
    scratch = os.path.join(tempfile.gettempdir(),
                           'rama_quick_' + os.path.basename(path))
    try:
        os.remove(scratch)
    except OSError:
        pass
    return scratch


def few(seq, k=1):
    """A prefix of an explicit configuration list under --quick, the whole list otherwise.

    Truncating the CONFIGURATION rather than the running TIME is what makes a quick baseline
    reproducible: the short run performs a prefix of exactly the same work, so its output is a
    function of the code, where a time-limited slice would depend on the machine.
    """
    return list(seq)[:k] if QUICK else seq
