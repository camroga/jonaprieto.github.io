module Jekyll
  module Watcher
    def custom_excludes(options)
      Array(options['exclude']).map { |e| Jekyll.sanitized_path(options['source'], e) unless e =~ /src/ }.compact
    end
  end
end
