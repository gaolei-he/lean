import os
import re
from generate import IMPORTS

def split_theorems(file_path, output_dir):
    # 读取文件内容
    with open(file_path, 'r', encoding='utf-8') as file:
        lean_code = file.read()

    # 使用正则表达式找到所有的定理
    theorems = re.findall(r'(theorem [^\s]*.*?:=.*?)(?=theorem|$)', lean_code, re.DOTALL)

    # 确保输出目录存在
    os.makedirs(output_dir, exist_ok=True)

    for theorem in theorems:
        # 提取定理名称并去掉后缀 '0'
        match = re.match(r'theorem ([^\s:]*)', theorem)
        if match:
            theorem_name = match.group(1)
            if theorem_name.endswith('0'):
                file_name = theorem_name[:-1] + '.lean'  # 去掉后缀 '0'
            else:
                file_name = theorem_name + '.lean'

            # 替换证明步骤为 ':= by lean_repl sorry'
            proof_replacement = ':= by lean_repl sorry'
            theorem_code = re.sub(r':=.*', proof_replacement, theorem, flags=re.DOTALL)

            # 将定理写入单独的文件
            with open(os.path.join(output_dir, file_name), 'w', encoding='utf-8') as theorem_file:
                theorem_file.write(IMPORTS + '\n' + theorem_code)

def split_theorems0(file_path, output_dir):
    # 读取文件内容
    with open(file_path, 'r', encoding='utf-8') as file:
        lean_code = file.read()

    # 使用正则表达式找到所有的定理
    theorems = re.findall(r'(theorem [^\s\(\[\{]*.*?:=.*?)(?=theorem|$)', lean_code, re.DOTALL)

    # 确保输出目录存在
    os.makedirs(output_dir, exist_ok=True)

    for theorem in theorems:
        # 提取定理名称
        match = re.match(r'theorem (?P<name>[^\s\(\[\{:]*)', theorem)
        if match:
            theorem_name = match.group('name')
            
            # 生成文件名
            file_name = theorem_name + '.lean'

            # 给定理名称后面加上字符 '0'
            theorem_name_with_0 = theorem_name + '0'

            # 替换定理名称
            theorem_code = theorem.replace(theorem_name, theorem_name_with_0, 1)

            # 替换证明步骤为 ':= by lean_repl sorry'
            proof_replacement = ':= by lean_repl sorry'
            theorem_code = re.sub(r':=.*', proof_replacement, theorem_code, flags=re.DOTALL)

            # 将定理写入单独的文件
            with open(os.path.join(output_dir, file_name), 'w', encoding='utf-8') as theorem_file:
                theorem_file.write(IMPORTS + '\n' + theorem_code)

def list_files(directory):
    filelist = []
    for file in os.listdir(directory):
        if os.path.isfile(os.path.join(directory, file)):
            print(file)
            filelist.append(file)
    return filelist

# 示例使用
input_file_path = "/home2/wanglei/Project/testfolder/ALL/sqrt.lean"
output_dir = '/home2/wanglei/Project/testfolder/root/sqrt'
split_theorems0(input_file_path, output_dir)
