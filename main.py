import torch

from lean_dojo import *
print("hello,开始了")
from model import policy_model
from model import value_model
print("hello,开始了")
from trainer import Trainer
print("hello,开始了")
from mcts import State
from mcts import Node
from mcts import MCTS
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM

# import ssl
# ssl._create_default_https_context = ssl._create_unverified_context

print("hello,开始了")

device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')

args = {
    'batch_size': 20,
    'numIters': 20,                                # Total number of training iterations
    'num_simulations': 100,                         # Total number of MCTS simulations to run when deciding on a move to play
    'numEps': 20,                                  # Number of full games (episodes) to run during each iteration
    'numItersForTrainExamplesHistory': 20,
    'epochs': 5,                                    # Number of epochs of training per iteration
    'checkpoint_path': 'latest.pth',                 # location to save latest set of weights
    'TACRIC_NUMBER': 4,
    # 'MAX_ROUND_NUMBER' : 10
}

# game = Connect2Game()
# board_size = game.get_board_size()
# action_size = game.get_action_size()

feature_size = 70  # 特征向量的size
policyModel = policy_model(feature_size*2, device)
valueModel = value_model(feature_size, device)
print("hello,开始了！！")

# repo = LeanGitRepo("https://github.com/yangky11/lean4-example", "a61b40b90afba0ee5a3357665a86f7d0bb57461d")
# theorem = Theorem(repo, "Lean4Example.lean", "hello_world")

# dojo, state = Dojo(theorem).__enter__()

# state = TacticState(pp='a b c : Nat\n⊢ a + b + c = a + c + b', id=0, message=None)
# state = TacticState(pp='n : Nat\n⊢ choose n 1 = n', id=0, message=None)
repo = LeanGitRepo(
    "https://github.com/Moyvbai/lean4-example",
    "87f9ea9a9d7cbc6dd9e116e04234c032720ca8dc",
)
theorem = Theorem(repo, "Lean4Example.lean", "idt1_Pascal's_Recurrence")
dojo, state = Dojo(theorem).__enter__()
print(state)
init_state = State(state)
node = Node()
node.set_state(init_state)

current_node = node
# mcts = MCTS(current_node)
# current_node = mcts.run()


trainer = Trainer(policyModel, valueModel, args)
print("马上开始训练")
trainer.learn(current_node)

print("开始搜索策略")
mcts = MCTS(current_node, policyModel, valueModel, args)
node = mcts.runmcts()