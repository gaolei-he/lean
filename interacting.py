from lean_dojo import *
import ssl
ssl._create_default_https_context = ssl._create_unverified_context


repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "a61b40b90afba0ee5a3357665a86f7d0bb57461d")
theorem = Theorem(repo, "Lean4Example.lean", "hello_world")
print(theorem)

dojo, state = Dojo(theorem).__enter__()

# state_error = dojo.run_tac(state_0, "rw [←add_assoc]")
# try:
#     if(state_error.error is not None):
#         print(state_error)
#         print(dojo.is_successful)
# except Exception as ex:
#     print(state_error)
#     print("unsuccessful")


# state_1 = dojo.run_tac(state_0, "rw [add_assoc]")
# try:
#     if(state_1.error is None):
#         print(state_1)
#         print(dojo.is_successful)
# except Exception as ex:
#     print(state_1)
#     print(dojo.is_successful)

# state_2 = dojo.run_tac(state_1, "rw [add_comm b]")
# try:
#     if(state_1.error is None):
#         print(state_2)
#         print(dojo.is_successful)
# except Exception as ex:
#     print(state_2)
#     print(dojo.is_successful)

# result = dojo.run_tac(state_2, "sorry")
# try:
#     if(result.error is None):
#         print(result)
#         print(dojo.is_successful)
# except Exception as ex:
#     if(result == ProofGivenUp()):
#         print(result)
#         print("unsuccessful")


def proof(state,tac):
    result = dojo.run_tac(state, tac)
    try:
        if(result.error is not None):  ## 证明失败，terminal = 1 ， reward = -1
            print(result)
            # print(dojo.is_successful)
            # print("证明失败，terminal = 1 ， reward = -1")
            return -1
    except Exception as ex:  ## 成功 or 证明未完成 or sorry or 超时
        if(dojo.is_successful == True): ## 证明成功
            print(result)
            # print(dojo.is_successful)
            # print("证明成功，terminal = 1 ， reward = 1")
            return 1
        elif(result == ProofGivenUp()):
            print(result)
            # print(dojo.is_successful)
            # print("证明放弃，terminal = 1 ， reward = -1")
            return -1
        else:
            print(result)
            # print(dojo.is_successful)
            print("证明未完成，terminal = 0 ， reward = 0")
            return result



tac_list = ["rw [←add_assoc]","rw [add_assoc]","rw [add_comm b]","sorry","rw [←add_assoc]"]
for tac in tac_list:
    s = state
    try:
        state = proof(state,tac)
        if(state == -1):
            print("证明结束，terminal = 1 ， reward = -1")
            state = s
        elif(state == 1):
            print("证明成功，terminal = 1 ， reward = 1")
            break
        else: ## 继续选择下一个策略进行证明
            continue
    except Exception as ex:
        print("RuntimeError")



# with Dojo(theorem) as (dojo, init_state):  # 获得一个state和随机从大模型生成的策略list中选择的一条策略，执行改策略返回新状态
#   print(init_state)
#   result = dojo.run_tac(init_state, "rw [add_assoc,add_comm b] ")
#   # assert isinstance(result, ProofFinished)
#   result = dojo.run_tac(result, "rw [←add_assoc]")
#   print(result)
#   print(dojo.is_successful)