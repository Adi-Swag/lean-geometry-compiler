import os
import signal
import json

from E3.utils import *
from subprocess import Popen, PIPE


class Checker:
    def __init__(
        self,
        nperms=3,
        binTime=15,
        approxTime=5,
        mode="skipApprox",
        tmp_path=os.path.join(ROOT_DIR, "tmp", "check"),
        result_path=os.path.join(ROOT_DIR, "results"),
    ):
        self.tmp_path = tmp_path
        os.makedirs(self.tmp_path, exist_ok=True)
        self.result_path = result_path
        os.makedirs(self.result_path, exist_ok=True)

        self.nPermutations = nperms
        self.equivSolverTime = binTime
        self.approxSolverTime = approxTime
        self.mode = mode

    def check(self, ground, test, instanceName):
        tmpFile = os.path.abspath(os.path.join(self.tmp_path, instanceName + ".lean"))
        with open(tmpFile, "w") as file:
            leanFile = format_lean_checker_file(ground, test)
            file.write(leanFile)
        outputJsonFile = os.path.abspath(os.path.join(self.result_path, instanceName + ".json"))
        command = [
            "lake",
            "env",
            "lean",
            "--run",
            tmpFile,
            instanceName,
            self.mode,
            str(self.nPermutations),
            str(self.equivSolverTime),
            str(self.approxSolverTime),
            "true",
            outputJsonFile,
        ]
        process = Popen(
            command, stdin=PIPE, stdout=PIPE, cwd=ROOT_DIR, preexec_fn=os.setsid
        )
        try:
            # Wait for process to finish and capture output for debugging
            stdout, stderr = process.communicate()
            # If the output JSON wasn't produced, log stdout/stderr to help debugging
            if not os.path.exists(outputJsonFile):
                try:
                    out_text = stdout.decode('utf-8', errors='ignore') if stdout else ''
                except Exception:
                    out_text = str(stdout)
                try:
                    err_text = stderr.decode('utf-8', errors='ignore') if stderr else ''
                except Exception:
                    err_text = str(stderr)
                print(f"E3 checker did not produce output JSON. stdout:\n{out_text}\nstderr:\n{err_text}")
                return False

            with open(outputJsonFile, "r", encoding="utf-8") as f:
                data = json.load(f)

            result = data.get(instanceName, {}).get("binary_check")
            return result == "equiv"
        except:
            # Try to terminate the child process group if it's still running.
            try:
                # Prefer using process.terminate() / kill() where possible
                if process.poll() is None:
                    try:
                        process.terminate()
                    except Exception:
                        pass
                    try:
                        # Give it a moment to exit gracefully
                        process.wait(timeout=1)
                    except Exception:
                        try:
                            process.kill()
                        except Exception:
                            pass
                # Finally attempt to kill the process group (may fail if already exited)
                try:
                    pgid = os.getpgid(process.pid)
                    os.killpg(pgid, signal.SIGTERM)
                except Exception:
                    pass
            except Exception:
                pass
            return False
