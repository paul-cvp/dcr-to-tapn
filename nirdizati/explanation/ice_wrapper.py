from pdpbox import info_plots
from pdpbox.utils import _get_grids

from src.encoding.common import retrieve_proper_encoder, get_encoded_logs
from src.encoding.models import ValueEncodings
from src.explanation.models import Explanation


def explain(ice_exp: Explanation, training_df, test_df, explanation_target, prefix_target):
    job = ice_exp.job
    training_df = training_df.drop(['trace_id'], 1)
    if job.encoding.value_encoding == ValueEncodings.BOOLEAN.value:
        training_df['label'] = training_df['label'].astype(bool).astype(int) + 1

    feature_grids, percentile_info = _get_grids(
        feature_values=training_df[explanation_target].values, num_grid_points=10, grid_type=None,
        percentile_range='percentile', grid_range=None)
    custom_grids = [x for x in range(int(feature_grids.min()), int(feature_grids.max() - 1))]

    fig, axes, summary_df = info_plots.target_plot(
        df = training_df,
        feature = explanation_target,
        feature_name = 'feature value',
        cust_grid_points = custom_grids,
        target = 'label',
        show_percentile = False
    )
    lists = list(training_df[explanation_target].values)
    indexs = [lists.index(x) for x in range(int(feature_grids.min()), int(feature_grids.max() - 1))]
    encoder = retrieve_proper_encoder(job)
    encoder.decode(training_df, job.encoding)
    values = training_df[explanation_target].values
    lst = []
    if job.encoding.value_encoding != ValueEncodings.BOOLEAN.value:
        for x in range(len(indexs) - 1):
            lst.append({'value': values[indexs[x]],
                        'label': summary_df['label'][x],
                        'count': int(summary_df['count'][x]),
                        })
    else:
        for x in range(summary_df.shape[0]):
            lst.append({'value': summary_df['display_column'][x],
                        'label': summary_df['label'][x],
                        'count': int(summary_df['count'][x]),
                        })
    return lst
