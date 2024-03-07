import threading
import subprocess

def start_server():
    directory = "/home/dc755/Portal-to-ISAbelle/"
    command = "sbt \"runMain pisa.server.PisaOneStageServer8000\""
    subprocess.run(command, shell=True, cwd=directory, text=True)