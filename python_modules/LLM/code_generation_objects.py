# Class for completion information
class CompletionInformation:
    """Class that contains information about an iteration"""
    def __init__(self, completion_count, prompt, gpt_output, verified, verified_goals, temperature, info, code, feedback, verification_time_taken):

        # Information about the completion
        self.specification_completion_number = completion_count

        # Information about the input
        self.temperature_used = temperature
        self.prompt_used = prompt

        # Information about the output
        self.gpt_output = gpt_output
        self.code = code
        self.feedback = feedback

        # Verification information
        self.is_verified = verified
        self.verified_goals_count = verified_goals
        self.completion_information = info
        self.verification_time = verification_time_taken

        try:
            if verified_goals is not None:
                total_goals = verified_goals.split("/")[1]
                verified_goals = verified_goals.split("/")[0]
                if int(total_goals) == 0:
                    self.passed_goals_percentage = 0
                else:
                    self.passed_goals_percentage = int(verified_goals) / int(total_goals)
            else:
                self.passed_goals_percentage = 0
        except:
            self.passed_goals_percentage = 0
            print(f"Error: Could not get the percentage of passed goals.  Verified goals: {verified_goals})")

    def to_dict(self):
        """ Function that converts the completion information to a dictionary"""
        return {
            "specification_completion_number": self.specification_completion_number,
            "temperature_used": self.temperature_used,
            "prompt_used": self.prompt_used,
            "gpt_output": self.gpt_output,
            "code": self.code,
            "feedback": self.feedback,
            "is_verified": self.is_verified,
            "verified_goals_count": self.verified_goals_count,
            "completion_information": self.completion_information,
            "verification_time": self.verification_time,
            "passed_goals_percentage": self.passed_goals_percentage
        }

# Class for iteration information
class IterationInformation:
    """Class that contains information about the iteration"""
    def __init__(self, iteration, max_completions_used):
        self.iteration_number = iteration
        self.is_verified = False
        self.verification_time_iteration = 0
        self.completions_used = 0
        self.completions = []
        self.max_completions_used = max_completions_used
        self.best_attempt_index = None
        self.best_attempt_feedback = None
        self.best_attempt_specification = None
        self.best_attempt_metric_percentage = None

    # Function that adds a completion to the iteration information
    def add_completion(self, completion_information):
        """Function that adds a completion to the iteration information
        Args:
            completion_information: The completion information that is added
        """
        # If attempted to add a completion that would exceed the maximum completions used, then raise an error
        if self.completions_used + 1 > self.max_completions_used:
            raise ValueError("Attempted to add a completion to the iteration information, but the maximum completions used would be exceeded.")

        self.completions.append(completion_information)
        self.completions_used += 1
        self.verification_time_iteration += completion_information.verification_time

        # Check if the specification and code is verified
        if completion_information.is_verified:
            self.is_verified = True

        # Get the metric percentage. , then goals
        if completion_information.passed_goals_percentage is not None:
            metric_percentage = completion_information.passed_goals_percentage
        else:
            metric_percentage = 0

        # If the new completion than the best attempt, then update the best attempt
        if self.best_attempt_index is None or metric_percentage > self.best_attempt_metric_percentage:
            self.best_attempt_index = completion_information.specification_completion_number
            self.best_attempt_feedback = completion_information.feedback
            self.best_attempt_metric_percentage = completion_information.passed_goals_percentage
            self.best_attempt_specification = completion_information.gpt_output

    def to_dict(self):
        """ Function that converts the iteration information to a dictionary"""
        return {
            "iteration_number": self.iteration_number,
            "is_verified": self.is_verified,
            "verification_time_iteration": self.verification_time_iteration,
            "completions_used": self.completions_used,
            "completions": [completion.to_dict() for completion in self.completions],
            "max_completions_used": self.max_completions_used,
            "best_attempt_index": self.best_attempt_index,
            "best_attempt_feedback": self.best_attempt_feedback,
            "best_attempt_specification": self.best_attempt_specification,
            "best_attempt_metric_percentage": self.best_attempt_metric_percentage
        }

# Class for the specification generation process
class SpecificationGenerationProcess:
    """Class that contains the specification generation process"""
    def __init__(self, iterations):
        self.total_completions_requested = 0
        self.total_completions_used = 0
        self.total_time_taken_verification = 0
        self.max_specification_improvement_iterations = iterations
        self.initial_specification_generation_information = []
        self.specification_improvement_information = []
        self.is_verified = False

    # Function that adds the initial specification generation information to the specification generation process
    def add_initial_specification_generation_information(self, initial_specification_generation_information):
        """Function that adds the initial specification generation information to the specification generation process
        Args:
            initial_specification_generation_information: The initial specification generation information that is added
        """
        self.initial_specification_generation_information.append(initial_specification_generation_information)

        # Update the total completions requested and used
        self.total_completions_requested += initial_specification_generation_information.max_completions_used
        self.total_completions_used += initial_specification_generation_information.completions_used
        self.total_time_taken_verification += initial_specification_generation_information.verification_time_iteration

        # Check if the specification is verified
        if initial_specification_generation_information.is_verified:
            self.is_verified = True

    def to_dict(self):
        """ Function that converts the specification generation process to a dictionary"""
        return {
            "total_completions_requested": self.total_completions_requested,
            "total_completions_used": self.total_completions_used,
            "total_time_taken_verification": self.total_time_taken_verification,
            "max_specification_improvement_iterations": self.max_specification_improvement_iterations,
            "initial_specification_generation_information": [info.to_dict() for info in self.initial_specification_generation_information],
            "specification_improvement_information": [info.to_dict() for info in self.specification_improvement_information],
            "is_verified": self.is_verified
        }

     # Function that adds the specification improvement information to the specification generation process
    def add_specification_improvement_information(self, specification_improvement_information):
        """Function that adds the specification improvement information to the specification generation process
        Args:
            specification_improvement_information: The specification improvement information that is added
        """
        self.specification_improvement_information.append(specification_improvement_information)

        # Update the total completions requested and used
        self.total_completions_requested += specification_improvement_information.max_completions_used
        self.total_completions_used += specification_improvement_information.completions_used
        self.total_time_taken_verification += specification_improvement_information.verification_time_iteration

        # Check if the specification is verified
        if specification_improvement_information.is_verified:
            self.is_verified = True
