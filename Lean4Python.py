from Lean4Gym import *
import os
import vllm
import heapq
from tqdm import *

class Lean4Python:
    def __init__(self, project_dir = "", import_content = [], goal = "") -> None:
        self.project_dir = project_dir
        self.import_content = import_content
        self.goal = goal
        self.tactics = []
        self.leangym = None

    def write_into_file(self, theorem_name:str = "interact_temp", interact=False):
        file_path = os.path.join(self.project_dir, theorem_name) + ".lean"
        with open(file_path, 'w') as file:
            if interact:
                file.write("import Lean4Repl\n")

            for _import_contnet in self.import_content:
                file.write(_import_contnet + "\n")

            file.write(f"theorem {theorem_name} {self.goal} := by \n")

            if interact:
                file.write("  lean_repl sorry\n")

            else:
                for _tactic in self.tactics:
                    file.write(f"  {_tactic}\n")

    def clear_goal(self):
        self.goal = ""
        self.tactics = []
    
    def clear(self):
        self.project_dir = ""
        self.import_content.clear()
        self.leangym = None
        self.clear_goal()


    def start_goal(self, goal:str):
        self.goal = goal
        self.write_into_file("interact_temp", interact=True)
        self.leangym = Lean4Gym(self.project_dir, "interact_temp.lean")
        return self.leangym.getInitState()

    def import_file(self, import_file:str):
        self.import_content.append(import_file)
    
    def run_tactic(self, state, tactic:str):
        self.tactics.append(tactic)
        return self.leangym.run_tactic(state, [tactic])

# 模型的prompt输入
def _prompt_proofstep(ts):
    prompt = f"[GOAL]{ts}[PROOFSTEP]"
    return prompt

# 去重排序
def _unique_sorted(texts, scores):
    texts_ = []
    scores_ = []
    for t, s in sorted(zip(texts, scores), key=lambda x: -x[1]):
        if t not in texts_:
            texts_.append(t)
            scores_.append(s)
    return texts_, scores_


# 模型输入产生输出
def generate_vllm(prompt, model, tokenizer, temperatures, num_samples, stop, max_tokens=256):
    texts, scores = [], []
    for temperature in temperatures:
        params = vllm.SamplingParams(
            n=num_samples,
            temperature=temperature,
            use_beam_search=temperature==0.0,
            max_tokens=max_tokens,
            stop=stop,
            logprobs=0,
            top_k=-1
        )
        outputs = model.generate([prompt], params, use_tqdm=False)

        # for tac in outputs[0].outputs:
        #     print(tac)
        

        if len(outputs) == 0:
            return [], []
        for output in outputs[0].outputs:
            text = output.text.replace(tokenizer.eos_token, '') 
            score = output.cumulative_logprob/max(len(output.token_ids), 1)
            texts.append(text)
            scores.append(score)

    texts, scores = _unique_sorted(texts, scores)
    return texts, scores


def search(init_state, lean:Lean4Gym, model, tokenizer, max_iters=int(1e6), num_samples=16,
            max_tokens=255, time_out=600, queue_max_count=int(1e6)):
    queue = [(0.0, [], init_state)]
    visited = set() 
    proof_finished = False 
    start = time.time()

    for iteration in trange(max_iters):
        if len(queue) == 0 or proof_finished:
            break

        current_time = time.time()

        if current_time - start > time_out or len(queue) > queue_max_count:
            print("theorem is not proved")
            break

        total_score, steps, state = heapq.heappop(queue)
        # state.print()

        visited.add(state.getTacticState())

        step_cands, step_scores = generate_vllm(
            _prompt_proofstep(state.getTacticState()),
            model,
            tokenizer,
            [0],
            num_samples=num_samples,
            stop=tokenizer.eos_token,
            max_tokens=max_tokens
        )
        step_cands = [s.strip() for s in step_cands]

        print(step_cands)
        # break

        for step, score in zip(step_cands, step_scores):
            # try:
                result = lean.run_tactic(state, [step])
                
                if result.getError() != None:
                    continue

                if result.isFinish():
                    proof_finished = True
                    
                    print("Theorem has proved!")
                    print(steps+[step])
                    return steps+[step]

                else:
                    if result.getTacticState() not in visited:
                        new_score = (total_score - score)
                        heapq.heappush(queue, (new_score, steps+[step], result)) 

            # except (Exception) as ex:
            #     print(ex)      
        


# lean.import("很多字符串")
# lean.start_goal("需要证明的定理")
# 后台要把上面的两个字符串的内容合并一个临时的lean文件中，再用我们lean4gym
# lean.run_tatic（“ 第一部 ”）
# lean.run_tatic（“  第二部 ”）