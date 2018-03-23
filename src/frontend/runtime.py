# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# 
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# or in the "license" file accompanying this file. This file is distributed 
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
# express or implied. See the License for the specific language governing 
# permissions and limitations under the License.

import os
import sys

class Runtime(object):
    def __init__(self):
        self.output_path = None
        self.paths = []
    def compile(self):
        raise NotImplementedError()
    def expect(self, val):
        raise NotImplementedError()
    def run(self):
        raise NotImplementedError()
    def add_path(self, path: str) -> None:
        self.paths.append(path)
    def _find_executable(self, name: str) -> str:
        options = [(name + ext) for ext in ["", ".exe", ".cmd", ".bat"]] if sys.platform == "win32" else [name]
        path = os.environ.get("PATH", "")
        paths = path.split(";" if sys.platform == "win32" and ":\\" in path else ":")
        for p in paths + self.paths:
            for o in options:
                full_path = os.path.join(p, o)
                if os.path.exists(full_path):
                    # this is the path, but quote it if needed for Windows
                    if sys.platform == "win32" and " " in full_path:
                        return '"{}"'.format(full_path)
                    return full_path
        error = """Couldn't find executable `{}` on your PATH.
Try specifying an additional search path with the --path argument""".format(name)
        raise Exception(error)