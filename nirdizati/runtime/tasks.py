import logging

from django_rq.decorators import job
from rest_framework import status

from src.core.core import runtime_calculate, replay_prediction_calculate
from src.encoding.models import Encoding
from src.jobs.models import JobStatuses, JobTypes, Job
from src.jobs.tasks import prediction_task
from src.jobs.ws_publisher import publish
from src.logs.models import Log
from src.split.models import Split
from src.utils.django_orm import duplicate_orm_row
from .replay import replay_core

logger = logging.getLogger(__name__)


@job("default", timeout='100h')
def runtime_task(job: Job):
    """ The function create a runtime task to ask a single prediction to the server

        :param job: job dictionary
    """
    logger.info("Start runtime task ID {}".format(job.id))
    try:
        job.status = JobStatuses.RUNNING.value
        job.save()
        result = runtime_calculate(job)
        job.results = {'result': str(result)}
        job.status = JobStatuses.COMPLETED.value
        job.error = ''
    except Exception as e:
        logger.error(e)
        job.status = JobStatuses.ERROR.value
        job.error = str(e.__repr__())
        raise e
    finally:
        job.save()
        publish(job)


@job("default", timeout='100h')
def replay_prediction_task(replay_prediction_job: Job, training_initial_job: Job, log: Log):
    """ The function create a replat prediction task to ask a single prediction to the server for a portion of a trace

        :param replay_prediction_job: job dictionary
        :param training_initial_job: job dictionary
        :param log: job dictionary
    """
    logger.info("Start replay_prediction task ID {}".format(replay_prediction_job.id))
    try:
        replay_prediction_job.status = JobStatuses.RUNNING.value
        replay_prediction_job.save()
        max_len = max(len(trace) for trace in log)
        if replay_prediction_job.encoding.prefix_length != max_len:
            prediction_job = create_prediction_job(training_initial_job, max_len)
            prediction_task(prediction_job.id)
            prediction_job.refresh_from_db()
            # new_replay_prediction_job = duplicate_orm_row(prediction_job)  #todo: replace with simple CREATE
            new_replay_prediction_job = Job.objects.create(
                created_date=prediction_job.created_date,
                modified_date=prediction_job.modified_date,
                error=prediction_job.error,
                status=prediction_job.status,
                type=prediction_job.type,
                create_models=prediction_job.create_models,
                case_id=prediction_job.case_id,
                event_number=prediction_job.event_number,
                gold_value=prediction_job.gold_value,
                results=prediction_job.results,
                parent_job=prediction_job.parent_job,
                split=prediction_job.split,
                encoding=prediction_job.encoding,
                labelling=prediction_job.labelling,
                clustering=prediction_job.clustering,
                predictive_model=prediction_job.predictive_model,
                evaluation=prediction_job.evaluation,
                hyperparameter_optimizer=prediction_job.hyperparameter_optimizer,
                incremental_train=prediction_job.incremental_train
            )
            new_replay_prediction_job.split = Split.objects.filter(pk=replay_prediction_job.split.id)[0]
            new_replay_prediction_job.type = JobTypes.REPLAY_PREDICT.value
            new_replay_prediction_job.parent_job = replay_prediction_job.parent_job
            new_replay_prediction_job.status = JobStatuses.CREATED.value
            replay_prediction_task(new_replay_prediction_job, prediction_job, log)
            return
        result_dict, events_for_trace = replay_prediction_calculate(replay_prediction_job, log)
        replay_prediction_job.results = dict(result_dict)
        replay_prediction_job.event_number = dict(events_for_trace)
        replay_prediction_job.status = JobStatuses.COMPLETED.value
        replay_prediction_job.error = ''
    except Exception as e:
        logger.error(e)
        replay_prediction_job.status = JobStatuses.ERROR.value
        replay_prediction_job.error = str(e.__repr__())
        raise e
    finally:
        replay_prediction_job.save()
        publish(replay_prediction_job)


@job("default", timeout='100h')
def replay_task(replay_job: Job, training_initial_job: Job) -> list:
    """ The function create a replay task to ask the server to demo the arriving of events

        :param replay_job: job dictionary
        :param training_initial_job: job dictionary
        :return: List of requests
    """
    logger.error("Start replay task ID {}".format(replay_job.id))
    requests = list()
    try:
        replay_job.status = JobStatuses.RUNNING.value
        replay_job.error = ''
        replay_job.save()
        requests = replay_core(replay_job, training_initial_job)
        replay_job.status = JobStatuses.COMPLETED.value
        for r in requests:
            if r.status_code != status.HTTP_201_CREATED:
                replay_job.error += [r]
    except Exception as e:
        logger.error(e)
        replay_job.status = JobStatuses.ERROR.value
        replay_job.error += [str(e.__repr__())]
        raise e
    finally:
        replay_job.save()
        publish(replay_job)
        return requests


def create_prediction_job(job: Job, max_len: int) -> Job:
    """ The function create a new prediction job to create a model when it isn't in the database

        :param job: job dictionary
        :param max_len: job dictionary
        :return: Job
    """
    # new_job = duplicate_orm_row(job)  #todo: replace with simple CREATE
    new_job = Job.objects.create(
        created_date=job.created_date,
        modified_date=job.modified_date,
        error=job.error,
        status=job.status,
        type=job.type,
        create_models=job.create_models,
        case_id=job.case_id,
        event_number=job.event_number,
        gold_value=job.gold_value,
        results=job.results,
        parent_job=job.parent_job,
        split=job.split,
        encoding=job.encoding,
        labelling=job.labelling,
        clustering=job.clustering,
        predictive_model=job.predictive_model,
        evaluation=job.evaluation,
        hyperparameter_optimizer=job.hyperparameter_optimizer,
        incremental_train=job.incremental_train
    )
    new_job.type = JobTypes.PREDICTION.value
    new_job.status = JobStatuses.CREATED.value
    # new_encoding = duplicate_orm_row(Encoding.objects.filter(pk=job.encoding.id)[0])  #todo: replace with simple CREATE
    new_encoding = Encoding.objects.create(
        data_encoding=job.encoding.data_encoding,
        value_encoding=job.encoding.value_encoding,
        add_elapsed_time=job.encoding.add_elapsed_time,
        add_remaining_time=job.encoding.add_remaining_time,
        add_executed_events=job.encoding.add_executed_events,
        add_resources_used=job.encoding.add_resources_used,
        add_new_traces=job.encoding.add_new_traces,
        features=job.encoding.features,
        prefix_length=job.encoding.prefix_length,
        padding=job.encoding.padding,
        task_generation_type=job.encoding.task_generation_type
    )
    new_encoding.prefix_length = max_len
    new_encoding.save()
    new_job.encoding = new_encoding
    new_job.create_models = True
    new_job.save()
    return new_job
